/-
Regression guard for graded matching families (`InfinitaryLogic/Scott/GradedMatching.lean`).

Every public theorem is *applied*, not only listed for its axioms.

* **`BFEquiv` is itself a graded system.**  With `R := BFEquiv`, the laws come from
  `BFEquiv.zero`, `BFEquiv.of_succ`, `BFEquiv.limit`, `BFEquiv.forth`, `BFEquiv.back` (and
  `BFEquiv.monotone` for the one-law form); the core theorem, at any height and at
  `height := α`, and the one-law form recover `BFEquiv` from a `BFEquiv` seed, for an
  arbitrary language, independent carrier universes and a free ordinal universe.
* **Pure sets: the empty tuple and repeated coordinates.**  On infinite pure sets the
  level-independent family "same equality pattern" is a graded matching family; through
  `bfEquiv_of_gradedMatching`, the empty tuples of `ℕ` and `ℤ` and the repeated-coordinate tuples
  `![3, 3]` and `![-1, -1]` are `BFEquiv` at every level.  **Negative:** `![3, 3]` and `![-1, 2]`
  are not `BFEquiv` even at level `0`.
* **Height zero, empty carrier.**  `Empty` and `Unit`, both with a nullary relation true: the
  family `SameAtomicType` (at every level) satisfies the laws at height `0` (forth and back are
  vacuous because `α + 1 ≤ 0` fails), and the empty tuples are `BFEquiv` at level `0`.
  **Negative:** they are not `BFEquiv` at level `1` (the point of `Unit` has no partner), so the
  height bound is doing the work.
* **Data-valued receipts.**  A receipt for `(a, b)` is a bijection `g : X ≃ Y` of pure sets with
  `g ∘ a = b` (a `Type`; receipts are far from unique); lowering keeps the receipt, extension
  answers `x` by `g x` and `y` by `g.symm y`.  Through `bfEquiv_of_gradedReceipt` (an actual
  receipt) and `bfEquiv_of_nonempty_gradedReceipt` (a `Nonempty` seed), `![3, 3]` in `ℕ` and
  its image in `ℤ` are `BFEquiv` at every level.
* **Negative control: the laws alone give nothing.**  `R := fun _ _ _ _ ↦ False` satisfies
  `atomic`, `lower`, `forth` and `back`; on `Unit` (nullary relation true) and `Bool` (false),
  the empty tuples are not `BFEquiv` at level `0`; hence no statement "laws imply `BFEquiv`"
  without a seed holds.
* **`down` is load-bearing.**  `Empty` with `S` true and `PEmpty` with `S` false: the family
  `R α _ _ _ := α = 1` satisfies the core's `atomic`, `limit`, `forth` and `back` at height `1`
  (forth and back vacuously, the carriers being empty) and has a seed at level `1`, but fails
  `down`; and the empty tuples are not `BFEquiv` at level `1`.  So the core's laws without
  `down` imply nothing.
* **Explicit universes.**  The `Type 1` carrier `ULift.{1} ℤ`, through
  `bfEquiv_of_gradedMatching.{0, 0, 0, 1, 0}` and `bfEquiv_of_gradedReceipt.{0, 0, 0, 1, 0, 1}`
  (receipts in `Type 1`).
* **Import closure** of the module: its only direct import is `Scott/BackAndForth`, and its
  transitive closure contains no Karp, Scott-formula, Scott-sentence, Montalbán-sentence,
  refinement-count, Scott-process, descriptive, method, model-theory, admissible or conditional
  module.

The module declarations and the guard's own declarations use only the standard axioms.

Run with: lake env lean scripts/check_graded_matching_regressions.lean
-/
import InfinitaryLogic.Scott.GradedMatching
import Mathlib.Tactic.FinCases

open Lean FirstOrder FirstOrder.Language

universe u v w w' uι

noncomputable section

namespace GradedMatchingGuard

/-! ### `BFEquiv` is itself a graded system -/

section Self

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- **The core with `R := BFEquiv`**, at any height: the laws are `BFEquiv`'s own lemmas. -/
theorem self_system {height α : Ordinal.{uι}} (hα : α ≤ height) {n : ℕ} {a : Fin n → M}
    {b : Fin n → N} (h : BFEquiv (L := L) α n a b) : BFEquiv (L := L) α n a b :=
  bfEquiv_of_gradedSystem (fun α n a b ↦ BFEquiv (L := L) α n a b)
    (fun h ↦ (BFEquiv.zero _ _).1 h) (fun _ h ↦ BFEquiv.of_succ h)
    (fun hl _ _ _ _ h β hβ ↦ (BFEquiv.limit _ hl _ _).1 h β hβ)
    (fun _ h ↦ BFEquiv.forth h) (fun _ h ↦ BFEquiv.back h) hα h

/-- **The core at `height := α`**, the form later bundled uses take. -/
theorem self_system_at_height {α : Ordinal.{uι}} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) α n a b) : BFEquiv (L := L) α n a b :=
  self_system (height := α) le_rfl h

/-- **The one-law form with `R := BFEquiv`**: `lower` is `BFEquiv.monotone`. -/
theorem self_matching {height α : Ordinal.{uι}} (hα : α ≤ height) {n : ℕ} {a : Fin n → M}
    {b : Fin n → N} (h : BFEquiv (L := L) α n a b) : BFEquiv (L := L) α n a b :=
  bfEquiv_of_gradedMatching (fun α n a b ↦ BFEquiv (L := L) α n a b)
    (fun h ↦ (BFEquiv.zero _ _).1 h) (fun hβα _ h ↦ BFEquiv.monotone hβα h)
    (fun {α _ _ _} _ h ↦ BFEquiv.forth (α := α) (by rwa [Order.succ_eq_add_one]))
    (fun {α _ _ _} _ h ↦ BFEquiv.back (α := α) (by rwa [Order.succ_eq_add_one])) hα h

end Self

/-! ### Pure sets: equality patterns -/

section Pure

attribute [local instance] Language.emptyStructure

/-- Two tuples have the same equality pattern. -/
def SamePattern {X : Type*} {Y : Type*} {n : ℕ} (a : Fin n → X) (b : Fin n → Y) : Prop :=
  ∀ i j, a i = a j ↔ b i = b j

theorem SamePattern.symm {X Y : Type*} {n : ℕ} {a : Fin n → X} {b : Fin n → Y}
    (h : SamePattern a b) : SamePattern b a := fun i j ↦ (h i j).symm

/-- In the empty language, the same equality pattern is the same atomic type. -/
theorem sameAtomicType_of_samePattern {X Y : Type*} {n : ℕ} {a : Fin n → X} {b : Fin n → Y}
    (h : SamePattern a b) : SameAtomicType (L := Language.empty) a b := by
  intro idx
  cases idx with
  | eq i j => exact h i j
  | rel R _ => exact isEmptyElim R

/-- A pattern extends by points that sit alike over the tuples. -/
theorem samePattern_snoc {X Y : Type*} {n : ℕ} {a : Fin n → X} {b : Fin n → Y}
    (h : SamePattern a b) {x : X} {y : Y} (hxy : ∀ i, a i = x ↔ b i = y) :
    SamePattern (Fin.snoc a x : Fin (n + 1) → X) (Fin.snoc b y) := by
  intro i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp
    | cast j =>
      simp only [Fin.snoc_last, Fin.snoc_castSucc]
      rw [eq_comm, hxy j, eq_comm]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simpa only [Fin.snoc_last, Fin.snoc_castSucc] using hxy i
    | cast j => simpa only [Fin.snoc_castSucc] using h i j

/-- **Forth for patterns**: into an infinite set, every point has a partner. -/
theorem samePattern_forth {X Y : Type*} [Infinite Y] {n : ℕ} {a : Fin n → X} {b : Fin n → Y}
    (h : SamePattern a b) (x : X) :
    ∃ y, SamePattern (Fin.snoc a x : Fin (n + 1) → X) (Fin.snoc b y) := by
  classical
  by_cases hx : ∃ i, a i = x
  · obtain ⟨i, rfl⟩ := hx
    exact ⟨b i, samePattern_snoc h fun k ↦ h k i⟩
  · obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (Finset.univ.image b)
    refine ⟨y, samePattern_snoc h fun k ↦ iff_of_false (fun e ↦ hx ⟨k, e⟩) fun e ↦ hy ?_⟩
    exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, e⟩

/-- **Back for patterns**: out of an infinite set, every point has a partner. -/
theorem samePattern_back {X Y : Type*} [Infinite X] {n : ℕ} {a : Fin n → X} {b : Fin n → Y}
    (h : SamePattern a b) (y : Y) :
    ∃ x, SamePattern (Fin.snoc a x : Fin (n + 1) → X) (Fin.snoc b y) := by
  obtain ⟨x, hx⟩ := samePattern_forth h.symm y
  exact ⟨x, hx.symm⟩

/-- **Same pattern gives `BFEquiv` at every level**, on infinite pure sets, through the one-law
form with the level-independent family `SamePattern`. -/
theorem pure_bfEquiv {X Y : Type*} [Infinite X] [Infinite Y] (α : Ordinal.{uι}) {n : ℕ}
    {a : Fin n → X} {b : Fin n → Y} (h : SamePattern a b) :
    BFEquiv (L := Language.empty) α n a b :=
  bfEquiv_of_gradedMatching (fun _ _ a b ↦ SamePattern a b) sameAtomicType_of_samePattern
    (fun _ _ h ↦ h) (fun _ h x ↦ samePattern_forth h x) (fun _ h y ↦ samePattern_back h y)
    le_rfl h

/-- **The empty tuple**: `ℕ` and `ℤ` over `![]` are `BFEquiv` at every level. -/
theorem empty_tuple (α : Ordinal.{uι}) :
    BFEquiv (L := Language.empty) α 0 (![] : Fin 0 → ℕ) (![] : Fin 0 → ℤ) :=
  pure_bfEquiv α fun i ↦ i.elim0

/-- **Repeated coordinates**: `![3, 3]` in `ℕ` and `![-1, -1]` in `ℤ` are `BFEquiv` at every
level. -/
theorem repeated_tuple (α : Ordinal.{uι}) :
    BFEquiv (L := Language.empty) α 2 ![(3 : ℕ), 3] ![(-1 : ℤ), -1] :=
  pure_bfEquiv α fun i j ↦ by fin_cases i <;> fin_cases j <;> simp

/-- **Negative**: `![3, 3]` and `![-1, 2]` differ in pattern, so are not `BFEquiv` at level
`0`. -/
theorem repeated_not_distinct :
    ¬ BFEquiv (L := Language.empty) (0 : Ordinal.{0}) 2 ![(3 : ℕ), 3] ![(-1 : ℤ), 2] := fun h ↦
  absurd (((BFEquiv.zero _ _).1 h (AtomicIdx.eq 0 1)).1 rfl) (by simp [AtomicIdx.holds])

/-! ### Data-valued receipts -/

/-- A receipt for `(a, b)`: a bijection carrying `a` to `b`.  It is data (a `Type`), and far
from unique. -/
def BijReceipt (X : Type*) (Y : Type*) (_ : Ordinal.{uι}) (n : ℕ) (a : Fin n → X)
    (b : Fin n → Y) : Type _ :=
  {g : X ≃ Y // ∀ i, g (a i) = b i}

theorem bijReceipt_atomic {X Y : Type*} {n : ℕ} {a : Fin n → X} {b : Fin n → Y}
    (ρ : BijReceipt.{uι} X Y 0 n a b) : SameAtomicType (L := Language.empty) a b :=
  sameAtomicType_of_samePattern fun i j ↦ by rw [← ρ.2 i, ← ρ.2 j, ρ.1.injective.eq_iff]

/-- A receipt extends along `g`. -/
def BijReceipt.snoc {X Y : Type*} {β γ : Ordinal.{uι}} {n : ℕ} {a : Fin n → X}
    {b : Fin n → Y} (ρ : BijReceipt.{uι} X Y β n a b) (x : X) :
    BijReceipt.{uι} X Y γ (n + 1) (Fin.snoc a x) (Fin.snoc b (ρ.1 x)) :=
  ⟨ρ.1, fun i ↦ by induction i using Fin.lastCases <;> simp [ρ.2]⟩

/-- **Receipts give `BFEquiv`**, through `bfEquiv_of_gradedReceipt`, at every level. -/
theorem receipt_bfEquiv {X Y : Type*} (α : Ordinal.{uι}) {n : ℕ} {a : Fin n → X}
    {b : Fin n → Y} (ρ : BijReceipt.{uι} X Y α n a b) :
    BFEquiv (L := Language.empty) α n a b :=
  bfEquiv_of_gradedReceipt (BijReceipt X Y) bijReceipt_atomic (fun _ _ ρ ↦ ⟨⟨ρ.1, ρ.2⟩⟩)
    (fun _ ρ x ↦ ⟨ρ.1 x, ⟨ρ.snoc x⟩⟩)
    (fun _ ρ y ↦ ⟨ρ.1.symm y, ⟨by simpa using ρ.snoc (ρ.1.symm y)⟩⟩) le_rfl ρ

/-- **A `Nonempty` receipt gives `BFEquiv`**, through `bfEquiv_of_nonempty_gradedReceipt`. -/
theorem nonempty_receipt_bfEquiv {X Y : Type*} (α : Ordinal.{uι}) {n : ℕ} {a : Fin n → X}
    {b : Fin n → Y} (ρ : Nonempty (BijReceipt.{uι} X Y α n a b)) :
    BFEquiv (L := Language.empty) α n a b :=
  bfEquiv_of_nonempty_gradedReceipt (BijReceipt X Y) bijReceipt_atomic
    (fun _ _ ρ ↦ ⟨⟨ρ.1, ρ.2⟩⟩)
    (fun _ ρ x ↦ ⟨ρ.1 x, ⟨ρ.snoc x⟩⟩)
    (fun _ ρ y ↦ ⟨ρ.1.symm y, ⟨by simpa using ρ.snoc (ρ.1.symm y)⟩⟩) le_rfl ρ

/-- **Concrete receipts**: `![3, 3]` in `ℕ` and its image in `ℤ`, from an actual receipt and from
a `Nonempty` one. -/
theorem concrete_receipts (α : Ordinal.{uι}) :
    BFEquiv (L := Language.empty) α 2 ![(3 : ℕ), 3]
        (fun i ↦ Equiv.intEquivNat.symm (![(3 : ℕ), 3] i)) ∧
      BFEquiv (L := Language.empty) α 2 ![(3 : ℕ), 3]
        (fun i ↦ Equiv.intEquivNat.symm (![(3 : ℕ), 3] i)) :=
  ⟨receipt_bfEquiv α ⟨Equiv.intEquivNat.symm, fun _ ↦ rfl⟩,
    nonempty_receipt_bfEquiv α ⟨⟨Equiv.intEquivNat.symm, fun _ ↦ rfl⟩⟩⟩

/-! ### Explicit universes -/

/-- **A `Type 1` carrier** through `bfEquiv_of_gradedMatching.{0, 0, 0, 1, 0}`. -/
theorem ulift_matching (α : Ordinal.{0}) :
    BFEquiv (L := Language.empty) α 2 ![(3 : ℕ), 3] ![ULift.up.{1} (-1 : ℤ), ULift.up (-1)] :=
  bfEquiv_of_gradedMatching.{0, 0, 0, 1, 0} (fun _ _ a b ↦ SamePattern a b)
    sameAtomicType_of_samePattern (fun _ _ h ↦ h) (fun _ h x ↦ samePattern_forth h x)
    (fun _ h y ↦ samePattern_back h y) le_rfl
    fun i j ↦ by fin_cases i <;> fin_cases j <;> simp

/-- **Receipts in `Type 1`** through `bfEquiv_of_gradedReceipt.{0, 0, 0, 1, 0, 1}`. -/
theorem ulift_receipt (α : Ordinal.{0}) :
    BFEquiv (L := Language.empty) α 2 ![(3 : ℕ), 3]
      (fun i ↦ (Equiv.intEquivNat.symm.trans Equiv.ulift.symm) (![(3 : ℕ), 3] i) :
        Fin 2 → ULift.{1} ℤ) :=
  bfEquiv_of_gradedReceipt.{0, 0, 0, 1, 0, 1} (BijReceipt ℕ (ULift.{1} ℤ)) bijReceipt_atomic
    (fun _ _ ρ ↦ ⟨⟨ρ.1, ρ.2⟩⟩) (fun _ ρ x ↦ ⟨ρ.1 x, ⟨ρ.snoc x⟩⟩)
    (fun _ ρ y ↦ ⟨ρ.1.symm y, ⟨by simpa using ρ.snoc (ρ.1.symm y)⟩⟩) le_rfl
    ⟨Equiv.intEquivNat.symm.trans Equiv.ulift.symm, fun _ ↦ rfl⟩

end Pure

/-! ### A nullary relation: height zero, and the negative control -/

section Nullary

/-- One nullary relation symbol `S`. -/
inductive NullRel : ℕ → Type
  /-- The nullary symbol. -/
  | S : NullRel 0

/-- The language with one nullary symbol. -/
abbrev nullLang : Language.{0, 0} := ⟨fun _ ↦ Empty, NullRel⟩

/-- The structure with nullary fact `s`. -/
abbrev nullStr (X : Type*) (s : Prop) : nullLang.Structure X where
  funMap f := Empty.elim f
  RelMap | .S, _ => s

instance : nullLang.Structure Empty := nullStr Empty True
instance : nullLang.Structure Unit := nullStr Unit True
instance : nullLang.Structure Bool := nullStr Bool False
instance : nullLang.Structure PEmpty.{1} := nullStr PEmpty False

/-- The empty tuples of `Empty` and `Unit` (both with `S` true) have the same atomic type. -/
theorem empty_unit_atomic :
    SameAtomicType (L := nullLang) (![] : Fin 0 → Empty) (![] : Fin 0 → Unit) := by
  intro idx
  cases idx with
  | eq i _ => exact i.elim0
  | rel R _ => cases R; exact Iff.rfl

/-- **Height zero, empty carrier**: `SameAtomicType`, at every level, satisfies the laws at
height `0` (forth and back are vacuous since `α + 1 ≤ 0` fails), and the empty tuples of `Empty`
and `Unit` are `BFEquiv` at level `0`. -/
theorem height_zero :
    BFEquiv (L := nullLang) (0 : Ordinal.{uι}) 0 (![] : Fin 0 → Empty) (![] : Fin 0 → Unit) :=
  bfEquiv_of_gradedMatching (fun _ _ a b ↦ SameAtomicType (L := nullLang) a b) (height := 0)
    id (fun _ _ h ↦ h) (fun h ↦ absurd h (by simp)) (fun h ↦ absurd h (by simp)) le_rfl
    empty_unit_atomic

/-- **Negative**: the same pair is not `BFEquiv` at level `1`: the point of `Unit` has no
partner in `Empty`. -/
theorem not_height_one :
    ¬ BFEquiv (L := nullLang) (1 : Ordinal.{uι}) 0 (![] : Fin 0 → Empty) (![] : Fin 0 → Unit) :=
  fun h ↦ by
    rw [show (1 : Ordinal.{uι}) = Order.succ 0 by simp] at h
    obtain ⟨x, _⟩ := BFEquiv.back h ()
    exact x.elim

/-- The everywhere-false family. -/
abbrev falseR : Ordinal.{0} → (n : ℕ) → (Fin n → Unit) → (Fin n → Bool) → Prop :=
  fun _ _ _ _ ↦ False

theorem false_atomic {n : ℕ} {a : Fin n → Unit} {b : Fin n → Bool} (h : falseR 0 n a b) :
    SameAtomicType (L := nullLang) a b := h.elim

theorem false_lower {height α β : Ordinal.{0}} {n : ℕ} {a : Fin n → Unit} {b : Fin n → Bool}
    (_ : β ≤ α) (_ : α ≤ height) (h : falseR α n a b) : falseR β n a b := h

theorem false_forth {height α : Ordinal.{0}} {n : ℕ} {a : Fin n → Unit} {b : Fin n → Bool}
    (_ : α + 1 ≤ height) (h : falseR (α + 1) n a b) (x : Unit) :
    ∃ y, falseR α (n + 1) (Fin.snoc a x) (Fin.snoc b y) := h.elim

theorem false_back {height α : Ordinal.{0}} {n : ℕ} {a : Fin n → Unit} {b : Fin n → Bool}
    (_ : α + 1 ≤ height) (h : falseR (α + 1) n a b) (y : Bool) :
    ∃ x, falseR α (n + 1) (Fin.snoc a x) (Fin.snoc b y) := h.elim

/-- `Unit` (with `S` true) and `Bool` (with `S` false) are not `BFEquiv` at level `0` over the
empty tuple. -/
theorem unit_bool_not_bfEquiv_zero :
    ¬ BFEquiv (L := nullLang) (0 : Ordinal.{0}) 0 (![] : Fin 0 → Unit) (![] : Fin 0 → Bool) :=
  fun h ↦ ((BFEquiv.zero _ _).1 h (AtomicIdx.rel NullRel.S Fin.elim0)).1 trivial

/-- **Negative control**: at every height the laws do not imply level-zero `BFEquiv`; the
everywhere-false family satisfies them, and the theorem applied to it needs a seed it has
none of. -/
theorem laws_alone_insufficient (height : Ordinal.{0}) :
    ¬ ∀ R : Ordinal.{0} → (n : ℕ) → (Fin n → Unit) → (Fin n → Bool) → Prop,
      (∀ {n a b}, R 0 n a b → SameAtomicType (L := nullLang) a b) →
      (∀ {α β n a b}, β ≤ α → α ≤ height → R α n a b → R β n a b) →
      (∀ {α n a b}, α + 1 ≤ height → R (α + 1) n a b →
        ∀ x, ∃ y, R α (n + 1) (Fin.snoc a x) (Fin.snoc b y)) →
      (∀ {α n a b}, α + 1 ≤ height → R (α + 1) n a b →
        ∀ y, ∃ x, R α (n + 1) (Fin.snoc a x) (Fin.snoc b y)) →
      BFEquiv (L := nullLang) (0 : Ordinal.{0}) 0 (![] : Fin 0 → Unit) (![] : Fin 0 → Bool) :=
  fun H ↦ unit_bool_not_bfEquiv_zero
    (H falseR false_atomic false_lower false_forth false_back)

/-- **The theorem on the everywhere-false family** is vacuous: it yields `BFEquiv` only from a
seed `False`. -/
theorem false_seed_only (height : Ordinal.{0}) (seed : falseR 0 0 ![] ![]) :
    BFEquiv (L := nullLang) (0 : Ordinal.{0}) 0 (![] : Fin 0 → Unit) (![] : Fin 0 → Bool) :=
  bfEquiv_of_gradedMatching falseR false_atomic (false_lower (height := height)) false_forth
    false_back zero_le seed

/-! #### `down` is load-bearing

On empty carriers forth and back are vacuous, so without `down` nothing carries a level-`1`
pair down to level `0`, where the nullary facts are compared. -/

/-- The family relating exactly at level `1`. -/
abbrev oneR : Ordinal.{0} → (n : ℕ) → (Fin n → Empty) → (Fin n → PEmpty.{1}) → Prop :=
  fun α _ _ _ ↦ α = 1

theorem one_atomic {n : ℕ} {a : Fin n → Empty} {b : Fin n → PEmpty.{1}} (h : oneR 0 n a b) :
    SameAtomicType (L := nullLang) a b := absurd h (by simp)

theorem one_limit {α : Ordinal.{0}} (hl : Order.IsSuccLimit α) (_ : α ≤ 1) {n : ℕ}
    {a : Fin n → Empty} {b : Fin n → PEmpty.{1}} (h : oneR α n a b) (β : Ordinal.{0})
    (_ : β < α) : oneR β n a b := by
  subst h
  exact absurd (by simpa using hl) (Order.not_isSuccLimit_succ (0 : Ordinal.{0}))

theorem one_forth {α : Ordinal.{0}} {n : ℕ} {a : Fin n → Empty} {b : Fin n → PEmpty.{1}}
    (_ : Order.succ α ≤ 1) (_ : oneR (Order.succ α) n a b) (x : Empty) :
    ∃ y, oneR α (n + 1) (Fin.snoc a x) (Fin.snoc b y) := x.elim

theorem one_back {α : Ordinal.{0}} {n : ℕ} {a : Fin n → Empty} {b : Fin n → PEmpty.{1}}
    (_ : Order.succ α ≤ 1) (_ : oneR (Order.succ α) n a b) (y : PEmpty.{1}) :
    ∃ x, oneR α (n + 1) (Fin.snoc a x) (Fin.snoc b y) := y.elim

/-- The family fails `down` at the bottom: related at level `succ 0 = 1`, not at level `0`. -/
theorem one_not_down : ¬ (oneR (Order.succ 0) 0 ![] ![] → oneR 0 0 ![] ![]) :=
  fun h ↦ absurd (h (by simp)) (by simp)

/-- `Empty` (with `S` true) and `PEmpty` (with `S` false) are not `BFEquiv` at level `1`. -/
theorem empty_pempty_not_bfEquiv_one :
    ¬ BFEquiv (L := nullLang) (1 : Ordinal.{0}) 0 (![] : Fin 0 → Empty)
      (![] : Fin 0 → PEmpty.{1}) := fun h ↦ by
  rw [show (1 : Ordinal.{0}) = Order.succ 0 by simp] at h
  exact ((BFEquiv.zero _ _).1 (BFEquiv.of_succ h) (AtomicIdx.rel NullRel.S Fin.elim0)).1 trivial

/-- **`down` is load-bearing**: over the core's law shapes at height `1`, `atomic`, `limit`,
`forth`, `back` and a seed at level `1` do not imply `BFEquiv` at level `1`; `oneR` satisfies
them all, on empty carriers with differing nullary facts. -/
theorem down_needed :
    ¬ ∀ R : Ordinal.{0} → (n : ℕ) → (Fin n → Empty) → (Fin n → PEmpty.{1}) → Prop,
      (∀ {n a b}, R 0 n a b → SameAtomicType (L := nullLang) a b) →
      (∀ {α}, Order.IsSuccLimit α → α ≤ 1 → ∀ {n a b}, R α n a b → ∀ β < α, R β n a b) →
      (∀ {α n a b}, Order.succ α ≤ 1 → R (Order.succ α) n a b →
        ∀ x, ∃ y, R α (n + 1) (Fin.snoc a x) (Fin.snoc b y)) →
      (∀ {α n a b}, Order.succ α ≤ 1 → R (Order.succ α) n a b →
        ∀ y, ∃ x, R α (n + 1) (Fin.snoc a x) (Fin.snoc b y)) →
      R 1 0 ![] ![] →
      BFEquiv (L := nullLang) (1 : Ordinal.{0}) 0 (![] : Fin 0 → Empty)
        (![] : Fin 0 → PEmpty.{1}) :=
  fun H ↦ empty_pempty_not_bfEquiv_one (H oneR one_atomic one_limit one_forth one_back rfl)

end Nullary

end GradedMatchingGuard

/-! ### Import closure and axiom audit -/

/-- The modules transitively imported by `m` (including `m`), read from the environment
header. -/
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

/-- Module-name prefixes no module of the closure may have. -/
def forbiddenPrefixes : List Name :=
  [`InfinitaryLogic.Karp, `InfinitaryLogic.Scott.Formula, `InfinitaryLogic.Scott.Sentence,
   `InfinitaryLogic.Scott.MontalbanSentence, `InfinitaryLogic.Scott.RefinementCount,
   `InfinitaryLogic.ScottProcess, `InfinitaryLogic.Descriptive, `InfinitaryLogic.Methods,
   `InfinitaryLogic.ModelTheory, `InfinitaryLogic.Admissible, `InfinitaryLogic.Conditional,
   `InfinitaryLogic.WIP]

run_cmd do
  let env ← getEnv
  let target := `InfinitaryLogic.Scott.GradedMatching
  let some idx := env.getModuleIdx? target
    | throwError "module {target} is not in the environment"
  let direct := (env.header.moduleData[idx.toNat]!).imports.toList.map (·.module)
  unless direct.filter (· != `Init) == [`InfinitaryLogic.Scott.BackAndForth] do
    throwError "[DIRECT IMPORTS] {target} imports {direct}, not only Scott.BackAndForth"
  let cl := importClosure env target
  let hits := cl.toList.filter fun m ↦ forbiddenPrefixes.any (·.isPrefixOf m)
  unless hits.isEmpty do
    throwError "[BROAD CONE] the closure of {target} reaches {hits}"

/-- The public declarations of the module. -/
def moduleDecls : List Name :=
  [`bfEquiv_of_gradedSystem, `bfEquiv_of_gradedMatching, `bfEquiv_of_nonempty_gradedReceipt,
   `bfEquiv_of_gradedReceipt].map (`FirstOrder.Language ++ ·)

/-- The guard's own declarations whose axioms are audited. -/
def guardDecls : List Name :=
  [`self_system, `self_system_at_height, `self_matching, `sameAtomicType_of_samePattern,
   `samePattern_snoc, `samePattern_forth, `samePattern_back, `pure_bfEquiv, `empty_tuple,
   `repeated_tuple, `repeated_not_distinct, `bijReceipt_atomic, `receipt_bfEquiv,
   `nonempty_receipt_bfEquiv, `concrete_receipts, `ulift_matching, `ulift_receipt,
   `empty_unit_atomic,
   `height_zero, `not_height_one, `false_atomic, `false_lower, `false_forth, `false_back,
   `unit_bool_not_bfEquiv_zero, `laws_alone_insufficient, `false_seed_only, `one_atomic,
   `one_limit, `one_forth, `one_back, `one_not_down, `empty_pempty_not_bfEquiv_one,
   `down_needed].map
    (`GradedMatchingGuard ++ ·)

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in moduleDecls ++ guardDecls do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "Graded-matching regression guard: OK (applied: the core at any height and at height \
    alpha and the one-law form with R := BFEquiv, laws from BFEquiv's own lemmas; equality \
    patterns on infinite pure sets through the one-law form, the empty tuple of N and Z and \
    the repeated tuples (3, 3) and (-1, -1) at every level, and (3, 3) against (-1, 2) not at \
    level 0; height zero with the empty carrier Empty against Unit, BFEquiv at level 0 and not \
    at level 1; bijection receipts (data, nonunique) through both receipt theorems; the \
    everywhere-false family satisfies every law while Unit and Bool, split by a nullary \
    relation, are not BFEquiv at level 0, so the laws alone imply nothing; down is load-bearing: \
    alpha = 1 meets the other core laws at height 1 on Empty (S true) against PEmpty (S false) \
    with a seed at level 1, which are not BFEquiv at level 1; the Type 1 carrier \
    ULift Z with explicit universes, receipts in Type 1; direct import only Scott.BackAndForth, \
    closure without Karp, Scott-formula, Scott-sentence, Montalban-sentence, refinement-count, \
    Scott-process, descriptive, method, model-theory, admissible or conditional modules; \
    standard axioms)"
