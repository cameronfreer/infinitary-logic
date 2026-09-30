/-
Regression guard for the semantic entries of tuples and the Scott process of a structure
(`InfinitaryLogic/ScottProcess/Semantic.lean`).

Every law below is *applied* to a concrete structure, not only listed for its axioms.  The
language `binLang.{u, v}` has one binary relation symbol and lives in arbitrary universes; the
carriers are `(ℕ, <)`, `ULift.{w} ℕ` with the lifted order, `(Fin 3, <)`, and `Pairs`, the
natural numbers with the equivalence relation whose classes are `{2k, 2k + 1}`.

* **Empty tuple**: every tuple restricts along `Fin 0 ↪ Fin n` to the entry of the empty tuple
  (`H_sf`), which is the only sentence of every level of the process (`scottProcessOf_Φ`), and
  is identified with the witness of Proposition 3.5 (`ScottProcess.existsUnique_mem_zero`).
* **Permutation**: `H_sf` along the swap of `Fin 2` sends the entry of `(0, 1)` to that of
  `(1, 0)`, and the two differ already at level `0` (`sf_zero_eq_sf_zero_iff`).
* **Forgotten coordinate**: `H_sf` along the non-surjective `Fin 1 ↪ Fin 2` hitting `1`, and
  its level-`0` form `H0_atomicType` on the atomic type of `(0, 1)`.
* **Repeated coordinates**: `exists_embedding_comp_eq` on the tuple `(5, 7, 5)`, and
  `exists_embedding_comp_eq_of_eq_iff` on `(5, 7, 5)` against `(1, 2, 1)` (one common `g`).
* **Common injective extension**: `exists_common_injective_extension` on the overlapping tuples
  `(0, 1)` and `(1, 2)`: `θ` has arity `4`, restricts to `(0, 1)` along `i_2`, satisfies
  `θ ∘ j = (1, 2)`, and `j` sends `0` to `1`.
* **Level `0`**: the atom `x_0 < x_1` read off `zeroEquiv_sf` and `atomicType_down_eq_true_iff`
  for `(0, 1)`; `(0)` and `(1)` have equal atomic types (`atomicType_eq_atomicType_iff`) and
  equal entries (`sf_zero_eq_sf_zero_iff`); the entry of `(0)` is the preimage of its
  `atomicType` under `zeroEquiv` (`isSf_zero`, `IsSf.unique`, `isSf_sf`).
* **Successor level**: `mem_E_sf_iff` in both directions on concrete one-point extensions;
  `(0)` and `(1)` have different entries at level `1` (the least element has no predecessor),
  with the same first component (`succEquiv_sf_fst`); a pair's entry lies in the extension set
  of its restriction's entry (`E_sf`); the extension set of the level-`1` entry
  of `(0)` is computed (`E_sf_snoc`): it is the single level-`0` entry of `(0, 1)`; so that
  entry is `mkSucc` of its level-`0` entry and this singleton (`isSf_add_one`, `eq_sf_iff`).
* **Level `ω`**: the entries of `(0)` and `(1)` in `(ℕ, <)` differ at level `ω` (`V_sf`,
  `limEquiv_sf`); an element of `Ψ_ω` is the entry of `(0)` iff its projections below `ω` are
  (`isSf_limit`, `eq_sf_iff`); the witness of `exists_isSf` at `ω` is that entry; in `Pairs`
  the entries of `(0)` and `(1)` agree at every level, including `ω`, by isomorphism transport
  (`sf_trans_equiv`) along the involution swapping `2k` and `2k + 1`.
* **Universes**: the entry of `(0)` in `ULift.{w} ℕ` equals the entry of `(0)` in `ℕ` over a
  language in universes `u, v` (`sf_trans_equiv` across carrier universes), and differs from
  that of `(1)` in `ℕ`.
* **Finite carriers**: the enumeration of `Fin 3` has no entry at any successor level
  (`not_isSf_add_one_of_card`).
* **The process**: the remark after Proposition 3.5 (`E_eq_of_mem_zero`) on
  `scottProcessOf binLang ℕ ω`, and Remark 3.4 (`image_H_eq`).
* **Simp normal forms**: plain `simp` closes the composites of `V`, `H`, `succEquiv`,
  `limEquiv` and `zeroEquiv` with `sf` (the `@[simp]` laws `V_sf`, `H_sf`, `succEquiv_sf_fst`,
  `limEquiv_sf`, `zeroEquiv_sf`).

The headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_semantic_entries_regressions.lean
-/
import InfinitaryLogic.ScottProcess.Semantic
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

/-- `(ℕ, <)`. -/
instance ltStructure : binLang.{u, v}.Structure ℕ where
  funMap f := PEmpty.elim f
  RelMap r x := match r, x with | .R, x => x 0 < x 1

/-- `(ULift ℕ, <)`. -/
instance ltStructureULift : binLang.{u, v}.Structure (ULift.{w} ℕ) where
  funMap f := PEmpty.elim f
  RelMap r x := match r, x with | .R, x => (x 0).down < (x 1).down

/-- `(Fin 3, <)`. -/
instance ltStructureFin : binLang.{u, v}.Structure (Fin 3) where
  funMap f := PEmpty.elim f
  RelMap r x := match r, x with | .R, x => x 0 < x 1

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

/-- The one-element tuple `(x)`. -/
def tup1 {M : Type*} (x : M) : Fin 1 ↪ M := ⟨fun _ ↦ x, fun a b _ ↦ Subsingleton.elim a b⟩

/-- The two-element tuple `(x, y)` of distinct elements. -/
def tup2 {M : Type*} {x y : M} (h : x ≠ y) : Fin 2 ↪ M := Function.Embedding.embFinTwo h

/-! ### Level `0` -/

/-- `0 ≠ 1` in `ℕ`. -/
theorem h01 : (0 : ℕ) ≠ 1 := zero_ne_one

/-- **Level `0`, read off `zeroEquiv_sf`**: the entry of `(0, 1)` assigns `true` to the atom
`x_0 < x_1` (`atomicType_down_eq_true_iff`). -/
theorem level0_atom :
    (zeroEquiv (relAtomic binLang.{u, v}) 2 (sf binLang.{u, v} 0 (tup2 h01))).down
      ⟨.rel BinRel.R id, trivial⟩ = true := by
  rw [zeroEquiv_sf, atomicType_down_eq_true_iff]
  exact (show (0 : ℕ) < 1 from zero_lt_one)

/-- **Level `0`** (`sf_zero_eq_sf_zero_iff`): `(0, 1)` and `(1, 0)` have different entries. -/
theorem level0_ne : sf binLang.{u, v} 0 (tup2 h01) ≠ sf binLang.{u, v} 0 (tup2 h01.symm) := by
  rw [Ne, sf_zero_eq_sf_zero_iff]
  intro h
  have := (h (.rel BinRel.R id)).1 (show (0 : ℕ) < 1 from zero_lt_one)
  exact absurd this (show ¬ (1 : ℕ) < 0 from Nat.not_lt_zero 1)

/-- All one-element tuples of `(ℕ, <)` have the same atomic type. -/
theorem sameAtomicType_one (x y : ℕ) :
    SameAtomicType (L := binLang.{u, v}) ⇑(tup1 x) ⇑(tup1 y) := by
  intro idx
  cases idx with
  | eq i j => exact iff_of_true rfl rfl
  | rel r f =>
    cases r
    exact iff_of_false (lt_irrefl x) (lt_irrefl y)

/-- **Level `0`** (`sf_zero_eq_sf_zero_iff`): all one-element tuples of `(ℕ, <)` have the same
entry. -/
theorem level0_one_eq (x y : ℕ) : sf binLang.{u, v} 0 (tup1 x) = sf binLang.{u, v} 0 (tup1 y) :=
  (sf_zero_eq_sf_zero_iff _ _).2 (sameAtomicType_one x y)

/-- **Atomic types of injective tuples** (`atomicType_eq_atomicType_iff`): `(0)` and `(1)` have
the same atomic type. -/
theorem atomicType_one_eq :
    atomicType binLang.{u, v} ⇑(tup1 (0 : ℕ)) = atomicType binLang.{u, v} ⇑(tup1 (1 : ℕ)) :=
  (atomicType_eq_atomicType_iff _ _).2 (sameAtomicType_one 0 1)

/-- **Level `0`, as a witness** (`isSf_zero`, `IsSf.unique`, `isSf_sf`): the level-`0` entry of
`(0)` is the element of `Ψ_0` that `zeroEquiv` sends to the atomic type of `(0)`. -/
theorem sf_zero_eq_symm :
    sf binLang.{u, v} 0 (tup1 (0 : ℕ)) =
      (zeroEquiv (relAtomic binLang.{u, v}) 1).symm
        (atomicType binLang.{u, v} ⇑(tup1 (0 : ℕ))) :=
  (isSf_sf 0 _).unique ((isSf_zero _ _).2 (Equiv.apply_symm_apply _ _))

/-! ### Projections: empty tuple, permutation, forgotten coordinate -/

/-- **Empty tuple** (`H_sf`): every tuple restricts along `Fin 0 ↪ Fin 2` to the entry of the
empty tuple. -/
theorem H_empty (α : Ordinal.{0}) {x y : ℕ} (h : x ≠ y) :
    H (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin 2) (sf binLang.{u, v} α (tup2 h)) =
      sf binLang.{u, v} α (Function.Embedding.ofIsEmpty : Fin 0 ↪ ℕ) := by
  rw [H_sf]
  congr 1
  exact Function.Embedding.ext fun i ↦ i.elim0

/-- The swap of `Fin 2`. -/
def swap2 : Fin 2 ↪ Fin 2 := (Equiv.swap 0 1).toEmbedding

/-- **Permutation** (`H_sf`): the swap sends the entry of `(0, 1)` to that of `(1, 0)`, which is a
different entry. -/
theorem H_swap (α : Ordinal.{0}) :
    H swap2 (sf binLang.{u, v} α (tup2 h01)) = sf binLang.{u, v} α (tup2 h01.symm) ∧
      H swap2 (sf binLang.{u, v} 0 (tup2 h01)) ≠ sf binLang.{u, v} 0 (tup2 h01) := by
  have hs : swap2.trans (tup2 h01) = tup2 h01.symm :=
    Function.Embedding.ext fun i ↦ by fin_cases i <;> rfl
  refine ⟨by rw [H_sf, hs], ?_⟩
  rw [H_sf, hs]
  exact fun h ↦ level0_ne h.symm

/-- The injection `Fin 1 ↪ Fin 2` hitting `1`; it forgets the coordinate `0`. -/
def j1 : Fin 1 ↪ Fin 2 := ⟨fun _ ↦ 1, fun a b _ ↦ Subsingleton.elim a b⟩

/-- **Forgotten coordinate** (`H_sf` along a non-surjective injection). -/
theorem H_forget (α : Ordinal.{0}) :
    H j1 (sf binLang.{u, v} α (tup2 h01)) = sf binLang.{u, v} α (tup1 (1 : ℕ)) := by
  rw [H_sf]
  rfl

/-- **Forgotten coordinate at level `0`** (`H0_atomicType`): the atomic type of `(0, 1)`
restricted along `j1` is the atomic type of `(1)`. -/
theorem H0_forget :
    (relAtomic binLang.{u, v}).H0 2 1 j1 (atomicType binLang.{u, v} ⇑(tup2 h01)) =
      atomicType binLang.{u, v} ⇑(tup1 (1 : ℕ)) :=
  H0_atomicType j1 _

/-! ### Repeated coordinates -/

/-- **Repeated coordinates** (`exists_embedding_comp_eq`) on `(5, 7, 5)`: the factor `g` identifies
the coordinates `0` and `2` and separates `0` and `1`, and `e` enumerates `{5, 7}`. -/
theorem factor_575 :
    ∃ (k : ℕ) (e : Fin k ↪ ℕ) (g : Fin 3 → Fin k),
      ⇑e ∘ g = ![5, 7, 5] ∧ Set.range e = {5, 7} ∧ g 0 = g 2 ∧ g 0 ≠ g 1 := by
  obtain ⟨k, e, g, he, hr, hp⟩ := exists_embedding_comp_eq ![5, 7, 5]
  refine ⟨k, e, g, he, ?_, (hp 0 2).1 rfl, fun h ↦ absurd ((hp 0 1).2 h) (by decide)⟩
  rw [hr]
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- **Repeated coordinates, two tuples** (`exists_embedding_comp_eq_of_eq_iff`): `(5, 7, 5)` and
`(1, 2, 1)` have the same equality pattern, so they factor through one common `g`, which
identifies the coordinates `0` and `2` and separates `0` and `1`. -/
theorem factor_575_121 :
    ∃ (k : ℕ) (e e' : Fin k ↪ ℕ) (g : Fin 3 → Fin k),
      ⇑e ∘ g = ![5, 7, 5] ∧ ⇑e' ∘ g = ![1, 2, 1] ∧ g 0 = g 2 ∧ g 0 ≠ g 1 := by
  obtain ⟨k, e, e', g, he, he'⟩ :=
    exists_embedding_comp_eq_of_eq_iff (![5, 7, 5] : Fin 3 → ℕ) (![1, 2, 1] : Fin 3 → ℕ)
      (by decide)
  refine ⟨k, e, e', g, he, he', e.injective ((congrFun he 0).trans (congrFun he 2).symm),
    fun h ↦ ?_⟩
  have h12 : (1 : ℕ) = 2 := (congrFun he' 0).symm.trans ((congrArg e' h).trans (congrFun he' 1))
  exact absurd h12 (by decide)

/-! ### Common injective extension -/

/-- `1 ≠ 2` in `ℕ`. -/
theorem h12 : (1 : ℕ) ≠ 2 := by decide

/-- **Common injective extension** (`exists_common_injective_extension`) of the overlapping
tuples `(0, 1)` and `(1, 2)` of `ℕ`: `θ` has arity `4`, restricts to `(0, 1)` along `i_2`, and
satisfies `θ ∘ j = (1, 2)`; the shared entry is detected, as `j` sends `0` to `1`. -/
theorem common_ext :
    ∃ (θ : Fin 4 ↪ ℕ) (j : Fin 2 ↪ Fin 4),
      (Fin.castLEEmb (Nat.le_add_right 2 2)).trans θ = tup2 h01 ∧ j.trans θ = tup2 h12 ∧
        θ 0 = 0 ∧ θ 1 = 1 ∧ θ (j 1) = 2 ∧ j 0 = 1 := by
  obtain ⟨θ, j, hθ, hj⟩ := exists_common_injective_extension (tup2 h01) (tup2 h12)
  have h0 : θ 0 = 0 := DFunLike.congr_fun hθ 0
  have h1 : θ 1 = 1 := DFunLike.congr_fun hθ 1
  have hj0 : θ (j 0) = 1 := DFunLike.congr_fun hj 0
  exact ⟨θ, j, hθ, hj, h0, h1, DFunLike.congr_fun hj 1, θ.injective (hj0.trans h1.symm)⟩

/-! ### Successor level -/

/-- `1 ∉ {0}`. -/
theorem one_not_mem : (1 : ℕ) ∉ Set.range (tup1 (0 : ℕ)) := fun ⟨_, h⟩ ↦ h01 h

/-- `0 ∉ {1}`. -/
theorem zero_not_mem : (0 : ℕ) ∉ Set.range (tup1 (1 : ℕ)) := fun ⟨_, h⟩ ↦ h01 h.symm

/-- **`E`-membership, backward direction** (`mem_E_sf_iff`): the level-`0` entry of `(1, 0)` lies
in the extension set of the level-`1` entry of `(1)`. -/
theorem mem_E_one : sf binLang.{u, v} 0 (tup2 h01.symm) ∈ E (sf binLang.{u, v} (0 + 1) (tup1 1)) :=
  mem_E_sf_iff.2 ⟨0, zero_not_mem, congrArg _ (Function.Embedding.ext fun i ↦ by
    fin_cases i <;> rfl)⟩

/-- **`E`-membership, forward direction** (`mem_E_sf_iff`): every member of the extension set of
the level-`1` entry of `(0)` is the entry of a fresh extension `(0, m)`, with `0 < m`; so the
entry of `(1, 0)` is not a member. -/
theorem not_mem_E_zero :
    sf binLang.{u, v} 0 (tup2 h01.symm) ∉ E (sf binLang.{u, v} (0 + 1) (tup1 0)) := by
  intro h
  obtain ⟨m, hm, he⟩ := mem_E_sf_iff.1 h
  rw [sf_zero_eq_sf_zero_iff] at he
  have hm0 : m ≠ 0 := fun h ↦ hm ⟨0, h.symm⟩
  have := (he (.rel BinRel.R id)).1 (show (0 : ℕ) < m from Nat.pos_of_ne_zero hm0)
  exact absurd this (show ¬ (1 : ℕ) < 0 from Nat.not_lt_zero 1)

/-- **Successor level**: `(0)` and `(1)` have the same entry at level `0` and different entries at
level `1`; the first component (`succEquiv_sf_fst`) is the common level-`0` entry. -/
theorem level1_ne :
    sf binLang.{u, v} (0 + 1) (tup1 (0 : ℕ)) ≠ sf binLang.{u, v} (0 + 1) (tup1 (1 : ℕ)) ∧
      (succEquiv (relAtomic binLang.{u, v}) 0 1 (sf binLang.{u, v} (0 + 1) (tup1 (0 : ℕ)))).1 =
        (succEquiv (relAtomic binLang.{u, v}) 0 1
          (sf binLang.{u, v} (0 + 1) (tup1 (1 : ℕ)))).1 := by
  refine ⟨fun h ↦ not_mem_E_zero (h ▸ mem_E_one), ?_⟩
  rw [succEquiv_sf_fst, succEquiv_sf_fst, level0_one_eq]

/-- **`E_sf`**: the entry of a pair lies in the extension set of the level-`1` entry of its
restriction along `i_1`. -/
theorem mem_E_restrict {x y : ℕ} (h : x ≠ y) :
    sf binLang.{u, v} 0 (tup2 h) ∈
      E (sf binLang.{u, v} (0 + 1) ((Fin.castLEEmb (Nat.le_succ 1)).trans (tup2 h))) := by
  rw [E_sf]
  exact ⟨_, rfl, rfl⟩

/-- **The extension set, computed** (`E_sf_snoc`, `sf_zero_eq_sf_zero_iff`): the extension set of
the level-`1` entry of `(0)` is the single level-`0` entry of `(0, 1)`: every fresh `m` is
above `0`. -/
theorem E_zero_eq :
    E (sf binLang.{u, v} (0 + 1) (tup1 (0 : ℕ))) = {sf binLang.{u, v} 0 (tup2 h01)} := by
  rw [E_sf_snoc]
  ext y
  simp only [Set.mem_range, Set.mem_singleton_iff, Subtype.exists]
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun h ↦ hm ⟨0, h.symm⟩
    rw [sf_zero_eq_sf_zero_iff]
    have ha : ∀ p : Fin 2, Fin.Embedding.snoc (tup1 (0 : ℕ)) hm p = if p = 0 then 0 else m := by
      intro p
      fin_cases p <;> rfl
    have hb : ∀ p : Fin 2, tup2 h01 p = if p = 0 then 0 else 1 := by
      intro p
      fin_cases p <;> rfl
    intro idx
    cases idx with
    | eq i j =>
      simp only [AtomicIdx.holds, EmbeddingLike.apply_eq_iff_eq]
    | rel r f =>
      cases r
      change _ < _ ↔ _ < _
      simp only [Function.comp_apply, ha, hb]
      generalize f 0 = p
      generalize f 1 = q
      fin_cases p <;> fin_cases q <;> simp [hm0]
  · rintro rfl
    exact ⟨1, one_not_mem, congrArg _ (Function.Embedding.ext fun i ↦ by fin_cases i <;> rfl)⟩

/-- **The successor unfolding** (`isSf_add_one`, `eq_sf_iff`, `isSf_sf`): the level-`1` entry
of `(0)` is `mkSucc` of its level-`0` entry and the singleton computed in `E_zero_eq`. -/
theorem sf_one_eq_mkSucc :
    sf binLang.{u, v} (0 + 1) (tup1 (0 : ℕ)) =
      mkSucc (sf binLang.{u, v} 0 (tup1 (0 : ℕ))) {sf binLang.{u, v} 0 (tup2 h01)}
        (Set.singleton_nonempty _) := by
  refine (eq_sf_iff.2 ((isSf_add_one 0 _ _).2 ⟨?_, ?_⟩)).symm
  · rw [V_mkSucc]
    exact isSf_sf 0 _
  · rw [E_mkSucc, ← E_zero_eq]
    exact ((isSf_add_one 0 _ _).1 (isSf_sf _ _)).2

/-! ### Level `ω` -/

/-- `0 + 1 ≤ ω`. -/
theorem one_le_ω : (0 : Ordinal.{0}) + 1 ≤ Ordinal.omega0 := by
  rw [zero_add]
  exact Ordinal.one_lt_omega0.le

/-- **Level `ω` in `(ℕ, <)`** (`V_sf`): `(0)` and `(1)` have different entries at level `ω`. -/
theorem levelω_ne :
    sf binLang.{u, v} Ordinal.omega0 (tup1 (0 : ℕ)) ≠
      sf binLang.{u, v} Ordinal.omega0 (tup1 (1 : ℕ)) := by
  intro h
  have := congrArg (V one_le_ω) h
  rw [V_sf, V_sf] at this
  exact level1_ne.1 this

/-- **Level `ω`, read as a thread** (`limEquiv_sf`): the entry at `ω` has the entry at `1` as its
entry at `1`. -/
theorem levelω_entry (a : Fin 1 ↪ ℕ) :
    (limEquiv (relAtomic binLang.{u, v}) Ordinal.isSuccLimit_omega0 1
      (sf binLang.{u, v} Ordinal.omega0 a)).1 1 Ordinal.one_lt_omega0 = sf binLang.{u, v} 1 a :=
  limEquiv_sf Ordinal.isSuccLimit_omega0 Ordinal.one_lt_omega0 a

/-- **The limit unfolding** (`isSf_limit`, `eq_sf_iff`): an element of `Ψ_ω` is the entry of
`(0)` iff each of its vertical projections below `ω` is the entry of `(0)` at that level. -/
theorem eq_sf_ω_iff (x : Ψ (relAtomic binLang.{u, v}) Ordinal.omega0 1) :
    x = sf binLang.{u, v} Ordinal.omega0 (tup1 (0 : ℕ)) ↔
      ∀ β (hβ : β < Ordinal.omega0), V hβ.le x = sf binLang.{u, v} β (tup1 (0 : ℕ)) := by
  rw [eq_sf_iff, isSf_limit Ordinal.isSuccLimit_omega0]
  exact forall₂_congr fun _ _ ↦ eq_sf_iff.symm

/-- **Existence** (`exists_isSf`, `eq_sf_iff`): the witness of `exists_isSf` at level `ω` for
`(0)` is the entry of `(0)`, and so differs from the entry of `(1)`. -/
theorem exists_isSf_ω :
    ∃ x, IsSf (L := binLang.{u, v}) Ordinal.omega0 (tup1 (0 : ℕ)) x ∧
      x = sf binLang.{u, v} Ordinal.omega0 (tup1 (0 : ℕ)) ∧
      x ≠ sf binLang.{u, v} Ordinal.omega0 (tup1 (1 : ℕ)) := by
  obtain ⟨x, hx⟩ := exists_isSf (L := binLang.{u, v}) Ordinal.omega0 (tup1 (0 : ℕ))
  have h := eq_sf_iff.2 hx
  exact ⟨x, hx, h, fun h' ↦ levelω_ne (h.symm.trans h')⟩

/-! ### Isomorphism transport -/

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

/-- **Isomorphism transport at every level** (`sf_trans_equiv`): in `Pairs`, the tuples `(0)` and
`(1)` have the same entry at every level, in particular at `ω`, although they differ in
`(ℕ, <)` already at level `1`. -/
theorem pairs_eq (α : Ordinal.{0}) :
    sf binLang.{u, v} α (tup1 (⟨0⟩ : Pairs)) = sf binLang.{u, v} α (tup1 (⟨1⟩ : Pairs)) := by
  rw [← sf_trans_equiv flipIso]
  rfl

/-- **Isomorphism transport at `ω`**, in contrast with `levelω_ne`. -/
theorem pairs_eq_ω :
    sf binLang.{u, v} Ordinal.omega0 (tup1 (⟨0⟩ : Pairs)) =
      sf binLang.{u, v} Ordinal.omega0 (tup1 (⟨1⟩ : Pairs)) :=
  pairs_eq _

/-- The lifting isomorphism `ULift ℕ ≃ ℕ` of ordered structures. -/
def downIso : ULift.{w} ℕ ≃[binLang.{u, v}] ℕ where
  toEquiv := Equiv.ulift
  map_fun' f := PEmpty.elim f
  map_rel' r _ := by
    cases r
    exact Iff.rfl

/-- **Universes** (`sf_trans_equiv` across carrier universes): over a language in universes
`u, v`, the entry of `(0)` in `ULift.{w} ℕ` equals the entry of `(0)` in `ℕ`, and differs from
the entry of `(1)` in `ℕ` at level `ω`. -/
theorem ulift_entries :
    sf binLang.{u, v} Ordinal.omega0 (tup1 (ULift.up.{w} 0 : ULift.{w} ℕ)) =
        sf binLang.{u, v} Ordinal.omega0 (tup1 (0 : ℕ)) ∧
      sf binLang.{u, v} Ordinal.omega0 (tup1 (ULift.up.{w} 0 : ULift.{w} ℕ)) ≠
        sf binLang.{u, v} Ordinal.omega0 (tup1 (1 : ℕ)) := by
  have h : sf binLang.{u, v} Ordinal.omega0 (tup1 (ULift.up.{w} 0 : ULift.{w} ℕ)) =
      sf binLang.{u, v} Ordinal.omega0 (tup1 (0 : ℕ)) := by
    rw [← sf_trans_equiv downIso]
    rfl
  exact ⟨h, h ▸ levelω_ne⟩

/-! ### Finite carriers -/

/-- **Finite carriers** (`not_isSf_add_one_of_card`): the enumeration of `Fin 3` has no entry at
any successor level. -/
theorem fin3_no_succ (α : Ordinal.{0}) (x : Ψ (relAtomic binLang.{u, v}) (α + 1) 3) :
    ¬ IsSf (M := Fin 3) (α + 1) (Function.Embedding.refl (Fin 3)) x :=
  not_isSf_add_one_of_card (by simp) _ α x

/-! ### The Scott process of `(ℕ, <)` -/

/-- The Scott process of `(ℕ, <)` of length `ω`. -/
abbrev Pℕ : ScottProcess (relAtomic binLang.{u, v}) Ordinal.omega0 :=
  scottProcessOf binLang ℕ Ordinal.omega0 Ordinal.omega0_pos

/-- `0 + 1 < ω`. -/
theorem zero_add_one_lt_ω : (0 : Ordinal.{0}) + 1 < Ordinal.omega0 := by
  rw [zero_add]
  exact Ordinal.one_lt_omega0

/-- **The sentences of the process** (`scottProcessOf_Φ`): every level has the entry of the empty
tuple as its only sentence. -/
theorem Pℕ_sentence (α : Ordinal.{0}) (hα : α < Ordinal.omega0) :
    Pℕ.{u, v}.Φ α hα 0 = {sf binLang.{u, v} α (Function.Embedding.ofIsEmpty : Fin 0 ↪ ℕ)} := by
  rw [scottProcessOf_Φ]
  ext φ
  refine ⟨?_, fun h ↦ ⟨_, h.symm⟩⟩
  rintro ⟨a, rfl⟩
  exact congrArg _ (Function.Embedding.ext fun i ↦ i.elim0)

/-- **Proposition 3.5 on the process** (`existsUnique_mem_zero`): the unique sentence of each
level is the entry of the empty tuple. -/
theorem Pℕ_sentence_unique (α : Ordinal.{0}) (hα : α < Ordinal.omega0)
    {φ : Ψ (relAtomic binLang.{u, v}) α 0} (hφ : φ ∈ Pℕ.{u, v}.Φ α hα 0) :
    φ = sf binLang.{u, v} α (Function.Embedding.ofIsEmpty : Fin 0 ↪ ℕ) :=
  (Pℕ.existsUnique_mem_zero α hα).unique hφ ⟨_, rfl⟩

/-- **The remark after Proposition 3.5 on the process** (`E_eq_of_mem_zero`): the extension set of
the level-`1` sentence is the level-`0` column `1`, the single entry of any one-element tuple. -/
theorem Pℕ_E_sentence :
    E (sf binLang.{u, v} (0 + 1) (Function.Embedding.ofIsEmpty : Fin 0 ↪ ℕ)) =
      {sf binLang.{u, v} 0 (tup1 (0 : ℕ))} := by
  rw [Pℕ.E_eq_of_mem_zero 0 zero_add_one_lt_ω ⟨_, rfl⟩, scottProcessOf_Φ]
  ext φ
  refine ⟨?_, fun h ↦ ⟨tup1 0, h.symm⟩⟩
  rintro ⟨a, rfl⟩
  have ha : a = tup1 (a 0) := Function.Embedding.ext fun i ↦ by fin_cases i; rfl
  exact Set.mem_singleton_iff.2 ((congrArg (sf binLang.{u, v} 0) ha).trans (level0_one_eq _ _))

/-- **Remark 3.4 on the process** (`image_H_eq`): the level-`1` column `1` is the image of the
column `2` under the forgetful injection `j1`. -/
theorem Pℕ_image_H :
    Pℕ.{u, v}.Φ 1 Ordinal.one_lt_omega0 1 = H j1 '' Pℕ.{u, v}.Φ 1 Ordinal.one_lt_omega0 2 :=
  Pℕ.image_H_eq 1 Ordinal.one_lt_omega0 j1

/-! ### Simp normal forms -/

/-- **Simp normal forms** (`@[simp]` on `V_sf`, `H_sf`, `succEquiv_sf_fst`, `limEquiv_sf`,
`zeroEquiv_sf`): `simp` alone pushes vertical and horizontal projections, in either order,
and the row equivalences through `sf`, without looping against `V_comp` and `H_comp`. -/
theorem simp_normal_forms {α β γ : Ordinal.{0}} (h1 : γ ≤ β) (h2 : β ≤ α) {n m l : ℕ}
    (j : Fin m ↪ Fin n) (k : Fin l ↪ Fin m) (a : Fin n ↪ ℕ) :
    V h1 (V h2 (sf binLang.{u, v} α a)) = sf binLang.{u, v} γ a ∧
      H k (H j (sf binLang.{u, v} α a)) = sf binLang.{u, v} α (k.trans (j.trans a)) ∧
      V h2 (H j (sf binLang.{u, v} α a)) = sf binLang.{u, v} β (j.trans a) ∧
      H j (V h2 (sf binLang.{u, v} α a)) = sf binLang.{u, v} β (j.trans a) ∧
      (succEquiv (relAtomic binLang.{u, v}) α n (sf binLang.{u, v} (α + 1) a)).1 =
        sf binLang.{u, v} α a ∧
      (limEquiv (relAtomic binLang.{u, v}) Ordinal.isSuccLimit_omega0 n
        (sf binLang.{u, v} Ordinal.omega0 a)).1 1 Ordinal.one_lt_omega0 =
        sf binLang.{u, v} 1 a ∧
      zeroEquiv (relAtomic binLang.{u, v}) n (sf binLang.{u, v} 0 a) =
        atomicType binLang.{u, v} ⇑a := by
  simp

end

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`InfinitaryLogic.ScottProcess.Semantic.atomicType,
   `InfinitaryLogic.ScottProcess.Semantic.atomicType_down_eq_true_iff,
   `InfinitaryLogic.ScottProcess.Semantic.H0_atomicType,
   `InfinitaryLogic.ScottProcess.Semantic.atomicType_eq_atomicType_iff,
   `InfinitaryLogic.ScottProcess.Semantic.IsSf,
   `InfinitaryLogic.ScottProcess.Semantic.isSf_zero,
   `InfinitaryLogic.ScottProcess.Semantic.isSf_add_one,
   `InfinitaryLogic.ScottProcess.Semantic.isSf_limit,
   `InfinitaryLogic.ScottProcess.Semantic.IsSf.unique,
   `InfinitaryLogic.ScottProcess.Semantic.exists_isSf,
   `InfinitaryLogic.ScottProcess.Semantic.sf,
   `InfinitaryLogic.ScottProcess.Semantic.isSf_sf,
   `InfinitaryLogic.ScottProcess.Semantic.eq_sf_iff,
   `InfinitaryLogic.ScottProcess.Semantic.zeroEquiv_sf,
   `InfinitaryLogic.ScottProcess.Semantic.V_sf,
   `InfinitaryLogic.ScottProcess.Semantic.succEquiv_sf_fst,
   `InfinitaryLogic.ScottProcess.Semantic.E_sf,
   `InfinitaryLogic.ScottProcess.Semantic.E_sf_snoc,
   `InfinitaryLogic.ScottProcess.Semantic.mem_E_sf_iff,
   `InfinitaryLogic.ScottProcess.Semantic.limEquiv_sf,
   `InfinitaryLogic.ScottProcess.Semantic.H_sf,
   `InfinitaryLogic.ScottProcess.Semantic.sf_zero_eq_sf_zero_iff,
   `InfinitaryLogic.ScottProcess.Semantic.sf_trans_equiv,
   `InfinitaryLogic.ScottProcess.Semantic.exists_common_injective_extension,
   `InfinitaryLogic.ScottProcess.Semantic.exists_embedding_comp_eq,
   `InfinitaryLogic.ScottProcess.Semantic.exists_embedding_comp_eq_of_eq_iff,
   `InfinitaryLogic.ScottProcess.Semantic.not_isSf_add_one_of_card,
   `InfinitaryLogic.ScottProcess.Semantic.scottProcessOf,
   `InfinitaryLogic.ScottProcess.Semantic.scottProcessOf_Φ,
   `level0_atom, `level0_ne, `sameAtomicType_one, `level0_one_eq, `atomicType_one_eq,
   `sf_zero_eq_symm, `H_empty, `H_swap, `H_forget, `H0_forget, `factor_575, `factor_575_121,
   `common_ext, `mem_E_one, `not_mem_E_zero, `level1_ne, `mem_E_restrict, `E_zero_eq,
   `sf_one_eq_mkSucc, `levelω_ne, `levelω_entry, `eq_sf_ω_iff, `exists_isSf_ω, `pairs_eq,
   `pairs_eq_ω, `ulift_entries, `fin3_no_succ, `Pℕ_sentence, `Pℕ_sentence_unique,
   `Pℕ_E_sentence, `Pℕ_image_H, `simp_normal_forms]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "semantic-entries regression guard: OK (applied: empty tuple, permutation and \
    forgotten coordinate via H_sf, H0_atomicType on j1; Proposition 3.5 via \
    existsUnique_mem_zero, its witness the empty-tuple entry; repeated-coordinate factoring \
    on (5, 7, 5) via exists_embedding_comp_eq and against (1, 2, 1) via \
    exists_embedding_comp_eq_of_eq_iff; exists_common_injective_extension on (0, 1) and \
    (1, 2); level 0 of (N, <) via zeroEquiv_sf, atomicType_down_eq_true_iff, \
    atomicType_eq_atomicType_iff, sf_zero_eq_sf_zero_iff, and isSf_zero with IsSf.unique and \
    isSf_sf; E-membership both ways via mem_E_sf_iff, E_sf, E_sf_snoc; successor level via \
    succEquiv_sf_fst, and sf 1 (0) as mkSucc via isSf_add_one and eq_sf_iff; level omega via \
    V_sf, limEquiv_sf, isSf_limit and exists_isSf; isomorphism transport on Pairs at every \
    level and across carrier universes; the finite boundary on Fin 3; scottProcessOf with \
    scottProcessOf_Φ, E_eq_of_mem_zero and image_H_eq; simp normal forms of V, H, succEquiv, \
    limEquiv and zeroEquiv on sf; headline declarations on standard axioms)"
