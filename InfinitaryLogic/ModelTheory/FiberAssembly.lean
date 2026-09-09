/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.ModelTheory.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Infix
import Mathlib.Data.Countable.Basic

/-!
# The labeled-fiber language and the row assembly

The first piece of the fiber construction (design note: nondecreasing-prefix variant): the
language of the assembled structure, its carrier, and the interpretation of every symbol.
Nothing else is proved here; the assembly and restriction theorems come next.

## Data

* a linear order `U` and **allowed sets** `A : ℕ → Set U`;
* a relational **component language** `Lc`, a default component `B_*`, and components `B u`
  for `u : U`, all `Lc`-structures.

## Rows, labels, fibers

* A **row** is an allowed word: a nondecreasing list `p` over `U` with `p[i] ∈ A i`
  (`IsAllowed`, `Row`).  The empty word is a row.
* A **label** is a nonempty word `τ` over `U`, admissible or not (`Label`), so the signature
  does not depend on allowed-word membership.
* The fiber of row `p` at label `τ` is the component `B (last τ)` if `τ` is a prefix of `p`,
  and `B_*` otherwise (`compIndex`, `Comp`).

## Carrier and language

The carrier is the disjoint union of the rows and of all fibers (`Carrier`: constructors `row`
and `pt`).  The language `lang U Lc` has, besides equality, the relation symbols

| symbol | arity | interpretation |
| --- | --- | --- |
| `row` | 1 | the element is a row |
| `own` | 2 | `own(x, r)`: `x` is a fiber point whose owner row is `r` |
| `lab τ` | 1 | the element is a fiber point with label `τ` |
| `lift R` for `R : Lc.Relations (l+1)` | `l+1` | all arguments lie in **one** fiber (same owner, same label) and `R` holds of their component elements there; mixed-fiber tuples are false |
| `lift0 R τ` for `R : Lc.Relations 0` | 1 | `lift0 R τ (r)`: `r` is a row and `R` holds in the fiber of `r` at label `τ` (owner-indexed lift of a component nullary symbol) |

The constructor uses allowed-word membership, order comparisons, prefixes, and the component
family.  **No well-founded initial segment `W` appears anywhere**: the assembly is independent
of `W` by construction.  The input order on rows and its successor relation are not symbols of
`lang`.

The symbol set is countable when `U` and the component symbols are (`instCountableSigmaSym`).
-/

namespace FirstOrder.Language

namespace FiberAssembly

universe u v w

/-! ### Rows and labels -/

/-- An allowed word: nondecreasing, with the `i`-th letter in `A i`. -/
def IsAllowed {U : Type u} [LinearOrder U] (A : ℕ → Set U) (p : List U) : Prop :=
  p.Pairwise (· ≤ ·) ∧ ∀ (i : ℕ) (h : i < p.length), p[i] ∈ A i

theorem isAllowed_nil {U : Type u} [LinearOrder U] (A : ℕ → Set U) : IsAllowed A [] :=
  ⟨List.Pairwise.nil, fun i h => absurd h (Nat.not_lt_zero i)⟩

/-- The rows: allowed words, the empty word included. -/
def Row {U : Type u} [LinearOrder U] (A : ℕ → Set U) : Type u := {p : List U // IsAllowed A p}

/-- The labels: nonempty words over `U`, admissible or not. -/
def Label (U : Type u) : Type u := {τ : List U // τ ≠ []}

/-- The last letter of a label. -/
def Label.last {U : Type u} (τ : Label U) : U := τ.1.getLast τ.2

/-! ### Fibers -/

/-- Which component sits at `(p, τ)`: `some (last τ)` if `τ` is a prefix of `p`, else `none`
(the default component). -/
def compIndex {U : Type u} [DecidableEq U] (p : List U) (τ : Label U) :
    Option U :=
  if τ.1 <+: p then some τ.last else none

theorem compIndex_of_prefix {U : Type u} [DecidableEq U] {p : List U} {τ : Label U}
    (h : τ.1 <+: p) : compIndex p τ = some τ.last := by
  unfold compIndex
  simp [h]

theorem compIndex_of_not_prefix {U : Type u} [DecidableEq U] {p : List U} {τ : Label U}
    (h : ¬ τ.1 <+: p) : compIndex p τ = none := by
  unfold compIndex
  simp [h]

/-- The component at an index: `B_*` at `none`, `B u` at `some u`. -/
def Comp {U : Type u} (Bstar : Type u) (B : U → Type u) : Option U → Type u
  | none => Bstar
  | some u => B u

instance instCompStructure {U : Type u} (Lc : Language.{v, w}) (Bstar : Type u) (B : U → Type u)
    [Lc.Structure Bstar] [∀ u, Lc.Structure (B u)] :
    ∀ o : Option U, Lc.Structure (Comp Bstar B o)
  | none => inferInstanceAs (Lc.Structure Bstar)
  | some u => inferInstanceAs (Lc.Structure (B u))

/-! ### The carrier -/

/-- The assembled carrier: rows, and the points of every fiber. -/
inductive Carrier {U : Type u} [LinearOrder U] (Bstar : Type u) (B : U → Type u)
    (A : ℕ → Set U) : Type u
  | row (p : Row A)
  | pt (p : Row A) (τ : Label U) (x : Comp Bstar B (compIndex p.1 τ))

/-! ### The language -/

/-- The relation symbols of the assembled language. -/
inductive Sym (U : Type u) (Lc : Language.{v, w}) : ℕ → Type (max u w)
  | row : Sym U Lc 1
  | own : Sym U Lc 2
  | lab (τ : Label U) : Sym U Lc 1
  | lift {l : ℕ} (R : Lc.Relations (l + 1)) : Sym U Lc (l + 1)
  | lift0 (R : Lc.Relations 0) (τ : Label U) : Sym U Lc 1

/-- The assembled language: relational, with the symbols of `Sym`. -/
def lang (U : Type u) (Lc : Language.{v, w}) : Language.{u, max u w} :=
  ⟨fun _ => PEmpty, Sym U Lc⟩

instance (U : Type u) (Lc : Language.{v, w}) : (lang U Lc).IsRelational :=
  fun _ => inferInstanceAs (IsEmpty PEmpty)

/-! ### The interpretation -/

section Interpretation

variable {U : Type u} [LinearOrder U] {Lc : Language.{v, w}} {Bstar : Type u} {B : U → Type u}
  [Lc.Structure Bstar] [∀ u, Lc.Structure (B u)] {A : ℕ → Set U}

/-- Interpretation of each symbol, by cases on the symbol. -/
def relMap : ∀ {n : ℕ}, Sym U Lc n → (Fin n → Carrier Bstar B A) → Prop
  | _, Sym.row, v => ∃ p, v 0 = Carrier.row p
  | _, Sym.own, v => ∃ p τ x, v 0 = Carrier.pt p τ x ∧ v 1 = Carrier.row p
  | _, Sym.lab τ, v => ∃ p x, v 0 = Carrier.pt p τ x
  | _, @Sym.lift _ _ l R, v => ∃ (p : Row A) (τ : Label U)
      (y : Fin (l + 1) → Comp Bstar B (compIndex p.1 τ)),
      (∀ i, v i = Carrier.pt p τ (y i)) ∧ Structure.RelMap R y
  | _, Sym.lift0 R τ, v => ∃ p : Row A, v 0 = Carrier.row p ∧
      @Structure.RelMap Lc (Comp Bstar B (compIndex p.1 τ)) _ 0 R Fin.elim0

/-- The assembled structure. -/
instance instStructure : (lang U Lc).Structure (Carrier Bstar B A) where
  funMap f _ := (f : PEmpty).elim
  RelMap R v := relMap R v

/-! ### Interpretation equations, one per symbol -/

theorem relMap_row (v : Fin 1 → Carrier Bstar B A) :
    Structure.RelMap (L := lang U Lc) Sym.row v ↔ ∃ p, v 0 = Carrier.row p := Iff.rfl

theorem relMap_own (v : Fin 2 → Carrier Bstar B A) :
    Structure.RelMap (L := lang U Lc) Sym.own v ↔
      ∃ p τ x, v 0 = Carrier.pt p τ x ∧ v 1 = Carrier.row p := Iff.rfl

theorem relMap_lab (τ : Label U) (v : Fin 1 → Carrier Bstar B A) :
    Structure.RelMap (L := lang U Lc) (Sym.lab τ) v ↔ ∃ p x, v 0 = Carrier.pt p τ x := Iff.rfl

theorem relMap_lift {l : ℕ} (R : Lc.Relations (l + 1)) (v : Fin (l + 1) → Carrier Bstar B A) :
    Structure.RelMap (L := lang U Lc) (Sym.lift R) v ↔
      ∃ (p : Row A) (τ : Label U) (y : Fin (l + 1) → Comp Bstar B (compIndex p.1 τ)),
        (∀ i, v i = Carrier.pt p τ (y i)) ∧ Structure.RelMap R y := Iff.rfl

theorem relMap_lift0 (R : Lc.Relations 0) (τ : Label U) (v : Fin 1 → Carrier Bstar B A) :
    Structure.RelMap (L := lang U Lc) (Sym.lift0 R τ) v ↔
      ∃ p : Row A, v 0 = Carrier.row p ∧
        @Structure.RelMap Lc (Comp Bstar B (compIndex p.1 τ)) _ 0 R Fin.elim0 := Iff.rfl

/-- Lifted relations never hold of a row argument. -/
theorem not_relMap_lift_of_row {l : ℕ} (R : Lc.Relations (l + 1))
    (v : Fin (l + 1) → Carrier Bstar B A) (i : Fin (l + 1)) (p : Row A)
    (hv : v i = Carrier.row p) : ¬ Structure.RelMap (L := lang U Lc) (Sym.lift R) v := by
  rintro ⟨q, τ, y, hy, -⟩
  have := hy i
  rw [hv] at this
  cases this

/-- **Mixed-fiber tuples are false**: a lifted relation holds only of arguments from one fiber
(same owner row and same label). -/
theorem relMap_lift_same_fiber {l : ℕ} (R : Lc.Relations (l + 1))
    (v : Fin (l + 1) → Carrier Bstar B A)
    (h : Structure.RelMap (L := lang U Lc) (Sym.lift R) v) (i j : Fin (l + 1)) :
    ∃ (p : Row A) (τ : Label U) (x y : Comp Bstar B (compIndex p.1 τ)),
      v i = Carrier.pt p τ x ∧ v j = Carrier.pt p τ y := by
  obtain ⟨p, τ, y, hy, -⟩ := h
  exact ⟨p, τ, y i, y j, hy i, hy j⟩

end Interpretation

/-! ### Countability of the symbols -/

/-- Symbols are countable when `U` and the component symbols are. -/
instance instCountableSigmaSym (U : Type u) (Lc : Language.{v, w}) [Countable U]
    [Countable (Σ n, Lc.Relations n)] : Countable (Σ n, Sym U Lc n) := by
  classical
  let code : (Σ n, Sym U Lc n) →
      (Unit ⊕ Unit ⊕ Label U ⊕ (Σ n, Lc.Relations n) ⊕ ((Σ n, Lc.Relations n) × Label U)) :=
    fun s => match s with
      | ⟨_, Sym.row⟩ => Sum.inl ()
      | ⟨_, Sym.own⟩ => Sum.inr (Sum.inl ())
      | ⟨_, Sym.lab τ⟩ => Sum.inr (Sum.inr (Sum.inl τ))
      | ⟨_, @Sym.lift _ _ l R⟩ => Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨l + 1, R⟩)))
      | ⟨_, Sym.lift0 R τ⟩ => Sum.inr (Sum.inr (Sum.inr (Sum.inr (⟨0, R⟩, τ))))
  have : Countable (Label U) := Subtype.countable
  refine Function.Injective.countable (f := code) ?_
  rintro ⟨n₁, s₁⟩ ⟨n₂, s₂⟩ h
  cases s₁ <;> cases s₂ <;> simp only [code, Sum.inl.injEq, Sum.inr.injEq, Sigma.mk.injEq,
    Prod.mk.injEq, reduceCtorEq] at h
  · rfl
  · rfl
  · subst h; rfl
  · obtain ⟨hl, hR⟩ := h
    have := Nat.succ_injective hl
    subst this
    cases hR
    rfl
  · obtain ⟨⟨-, hR⟩, hτ⟩ := h
    cases hR; subst hτ; rfl

end FiberAssembly

end FirstOrder.Language
