/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.BackAndForth

/-!
# Graded matching families imply back-and-forth equivalence

Let `R α n a b` be a family of relations between `n`-tuples `a` of `M` and `b` of `N`, graded by
ordinals `α` up to a height bound `height`.  Suppose that `R` is atomic at level `0` (it implies
`SameAtomicType`), that it lowers, and that at successor levels it has the forth and back
extension properties one level down.  Then every pair related at a level `α ≤ height` is
`α`-back-and-forth equivalent: `R α n a b → BFEquiv α n a b`.  This is the only ordinal
induction of the module (`bfEquiv_of_gradedSystem`); every other theorem is derived from it.

This is ordinal-budget matching: the height is an arbitrary ordinal budget, not required to be
countable; countable budgets are the immediate application.

No new notion of back-and-forth equivalence is introduced: the conclusion is the existing
`BFEquiv` of `Scott/BackAndForth.lean`, unfolded through `BFEquiv.zero`, `BFEquiv.succ` and
`BFEquiv.limit`.  The module is the foundation of the graded-system work (P2), not a second,
competing interface: the later bundled graded-system and closure adapters reuse this one ordinal
induction, with `height := α`.

## The seed is a separate premise

The laws (atomic, lowering, forth, back) are closure conditions, and the empty family
`R := fun _ _ _ _ ↦ False` satisfies all of them vacuously.  They therefore say nothing about any
particular pair: each theorem takes, besides the laws, a *seed* `R α n a b` at the pair and
level of interest, and concludes `BFEquiv` only there.

## Conventions

* **Ordinals.**  The ordinal universe `uι` is free, as in `BFEquiv`; `Ordinal.{0}` is one
  instance.  The core theorem states successors as `Order.succ α`, the form `BFEquiv.succ` uses;
  the one-law form `bfEquiv_of_gradedMatching` and the receipt forms state them as `α + 1`,
  which is `Order.succ α` by `Order.succ_eq_add_one`.
* **Height.**  Every law is required only at levels `≤ height`.  The core theorem has separate
  `down` and `limit` clauses, so that a family which is not antitone (only one-step lowering and
  limit lowering) can be used, in particular with `height := α`.
* **Generality.**  The statements are proved without the `[L.IsRelational]` instance, because
  `BFEquiv`'s own lemmas omit it.  The carrier universes `w` and `w'` are independent; there is
  no countability or nonemptiness assumption on `M`, `N` or `L`; tuples may be empty or have
  repeated coordinates; `R` need not be symmetric; and receipts need not be unique and may change
  under lowering.

## Main declarations

* `bfEquiv_of_gradedSystem`: the core.  From `atomic` (`R 0 → SameAtomicType`), `down`
  (`R (succ α) → R α` for `succ α ≤ height`), `limit` (`R α → R β` for `β < α`, when
  `Order.IsSuccLimit α` and `α ≤ height`), `forth` and `back` (for `succ α ≤ height`, an
  `R (succ α)` pair extends by any point on one side to an `R α` pair), `α ≤ height` and a seed
  `R α n a b`, conclude `BFEquiv α n a b`.
* `bfEquiv_of_gradedMatching`: the same with one lowering law `lower` (`β ≤ α ≤ height` and
  `R α → R β`) in place of `down` and `limit`, and with successors written `α + 1`.
* `bfEquiv_of_gradedReceipts`: for a `Type r`-valued family `Receipt` whose laws consume a receipt
  and return `Nonempty` receipts, a seed `Nonempty (Receipt α n a b)` gives `BFEquiv α n a b`.
* `bfEquiv_of_gradedReceipt`: the same from an actual receipt `Receipt α n a b`.

## Import boundary

The module imports only `Scott/BackAndForth.lean`: no Karp theory, no Scott-formula or
Scott-sentence construction, no descriptive set theory, no model-theoretic, method, admissible
or conditional module.
-/

universe u v w w' uι r

namespace FirstOrder.Language

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- **Graded systems give back-and-forth equivalence.**  A family `R`, graded by ordinals up to
`height`, that is atomic at level `0`, lowers one step at successors (`down`), lowers to every
smaller level at successor limits (`limit`), and has the forth and back properties one level
down at successors, relates only `BFEquiv` pairs: a seed `R α n a b` with `α ≤ height` gives
`BFEquiv α n a b`.  This is the module's only ordinal induction. -/
theorem bfEquiv_of_gradedSystem
    (R : Ordinal.{uι} → (n : ℕ) → (Fin n → M) → (Fin n → N) → Prop) {height : Ordinal.{uι}}
    (atomic : ∀ {n a b}, R 0 n a b → SameAtomicType (L := L) a b)
    (down : ∀ {α n a b}, Order.succ α ≤ height → R (Order.succ α) n a b → R α n a b)
    (limit : ∀ {α}, Order.IsSuccLimit α → α ≤ height →
      ∀ {n a b}, R α n a b → ∀ β < α, R β n a b)
    (forth : ∀ {α n a b}, Order.succ α ≤ height → R (Order.succ α) n a b →
      ∀ x : M, ∃ y : N, R α (n + 1) (Fin.snoc a x) (Fin.snoc b y))
    (back : ∀ {α n a b}, Order.succ α ≤ height → R (Order.succ α) n a b →
      ∀ y : N, ∃ x : M, R α (n + 1) (Fin.snoc a x) (Fin.snoc b y))
    {α : Ordinal.{uι}} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hα : α ≤ height) (seed : R α n a b) : BFEquiv (L := L) α n a b := by
  induction α using Ordinal.limitRecOn generalizing n a b with
  | zero => exact (BFEquiv.zero a b).2 (atomic seed)
  | add_one β ih =>
    rw [← Order.succ_eq_add_one] at hα seed ⊢
    have hβ : β ≤ height := (Order.le_succ β).trans hα
    refine (BFEquiv.succ β a b).2 ⟨ih hβ (down hα seed), fun x ↦ ?_, fun y ↦ ?_⟩
    · obtain ⟨y, hy⟩ := forth hα seed x
      exact ⟨y, ih hβ hy⟩
    · obtain ⟨x, hx⟩ := back hα seed y
      exact ⟨x, ih hβ hx⟩
  | limit β hβ ih =>
    exact (BFEquiv.limit β hβ a b).2 fun γ hγ ↦
      ih γ hγ (hγ.le.trans hα) (limit hβ hα seed γ hγ)

/-- **Graded matching families give back-and-forth equivalence.**  A family `R`, graded by
ordinals up to `height`, that is atomic at level `0`, lowers (`β ≤ α ≤ height` and `R α` give
`R β`), and has the forth and back properties from level `α + 1 ≤ height` to level `α`, relates
only `BFEquiv` pairs: a seed `R α n a b` with `α ≤ height` gives `BFEquiv α n a b`.  Derived
from `bfEquiv_of_gradedSystem`. -/
theorem bfEquiv_of_gradedMatching
    (R : Ordinal.{uι} → (n : ℕ) → (Fin n → M) → (Fin n → N) → Prop) {height : Ordinal.{uι}}
    (atomic : ∀ {n a b}, R 0 n a b → SameAtomicType (L := L) a b)
    (lower : ∀ {α β n a b}, β ≤ α → α ≤ height → R α n a b → R β n a b)
    (forth : ∀ {α n a b}, α + 1 ≤ height → R (α + 1) n a b →
      ∀ x : M, ∃ y : N, R α (n + 1) (Fin.snoc a x) (Fin.snoc b y))
    (back : ∀ {α n a b}, α + 1 ≤ height → R (α + 1) n a b →
      ∀ y : N, ∃ x : M, R α (n + 1) (Fin.snoc a x) (Fin.snoc b y))
    {α : Ordinal.{uι}} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hα : α ≤ height) (seed : R α n a b) : BFEquiv (L := L) α n a b :=
  bfEquiv_of_gradedSystem R atomic (fun h hR ↦ lower (Order.le_succ _) h hR)
    (fun _ h _ _ _ hR β hβ ↦ lower hβ.le h hR)
    (fun h hR ↦ by rw [Order.succ_eq_add_one] at h hR; exact forth h hR)
    (fun h hR ↦ by rw [Order.succ_eq_add_one] at h hR; exact back h hR)
    hα seed

/-- **Graded receipts give back-and-forth equivalence.**  `Receipt α n a b` is data witnessing
that `a` and `b` match at level `α`; the laws consume a receipt and return `Nonempty` receipts,
which need not be unique and may change under lowering.  A seed `Nonempty (Receipt α n a b)`
with `α ≤ height` gives `BFEquiv α n a b`.  This is `bfEquiv_of_gradedMatching` applied to
`fun α n a b ↦ Nonempty (Receipt α n a b)`. -/
theorem bfEquiv_of_gradedReceipts
    (Receipt : Ordinal.{uι} → (n : ℕ) → (Fin n → M) → (Fin n → N) → Type r)
    {height : Ordinal.{uι}}
    (atomic : ∀ {n a b}, Receipt 0 n a b → SameAtomicType (L := L) a b)
    (lower : ∀ {α β n a b}, β ≤ α → α ≤ height → Receipt α n a b → Nonempty (Receipt β n a b))
    (forth : ∀ {α n a b}, α + 1 ≤ height → Receipt (α + 1) n a b →
      ∀ x : M, ∃ y : N, Nonempty (Receipt α (n + 1) (Fin.snoc a x) (Fin.snoc b y)))
    (back : ∀ {α n a b}, α + 1 ≤ height → Receipt (α + 1) n a b →
      ∀ y : N, ∃ x : M, Nonempty (Receipt α (n + 1) (Fin.snoc a x) (Fin.snoc b y)))
    {α : Ordinal.{uι}} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hα : α ≤ height) (seed : Nonempty (Receipt α n a b)) : BFEquiv (L := L) α n a b :=
  bfEquiv_of_gradedMatching (fun α n a b ↦ Nonempty (Receipt α n a b))
    (fun ⟨ρ⟩ ↦ atomic ρ) (fun hβα h ⟨ρ⟩ ↦ lower hβα h ρ)
    (fun h ⟨ρ⟩ ↦ forth h ρ) (fun h ⟨ρ⟩ ↦ back h ρ) hα seed

/-- **A graded receipt gives back-and-forth equivalence**: `bfEquiv_of_gradedReceipts` with an
actual receipt `Receipt α n a b` as the seed. -/
theorem bfEquiv_of_gradedReceipt
    (Receipt : Ordinal.{uι} → (n : ℕ) → (Fin n → M) → (Fin n → N) → Type r)
    {height : Ordinal.{uι}}
    (atomic : ∀ {n a b}, Receipt 0 n a b → SameAtomicType (L := L) a b)
    (lower : ∀ {α β n a b}, β ≤ α → α ≤ height → Receipt α n a b → Nonempty (Receipt β n a b))
    (forth : ∀ {α n a b}, α + 1 ≤ height → Receipt (α + 1) n a b →
      ∀ x : M, ∃ y : N, Nonempty (Receipt α (n + 1) (Fin.snoc a x) (Fin.snoc b y)))
    (back : ∀ {α n a b}, α + 1 ≤ height → Receipt (α + 1) n a b →
      ∀ y : N, ∃ x : M, Nonempty (Receipt α (n + 1) (Fin.snoc a x) (Fin.snoc b y)))
    {α : Ordinal.{uι}} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hα : α ≤ height) (seed : Receipt α n a b) : BFEquiv (L := L) α n a b :=
  bfEquiv_of_gradedReceipts Receipt atomic lower forth back hα ⟨seed⟩

end FirstOrder.Language
