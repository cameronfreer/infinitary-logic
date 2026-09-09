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
# The labeled-fiber language, the generic row assembly, and its prefix specialization

A **row assembly** glues a family of component structures into one structure: a set of rows,
and for every row `r` and every label `τ` a fiber `C r τ` carrying a component structure.  The
generic assembly is parameterized by an arbitrary row type `R` and fiber family
`C : R → Label U → Type`, so that different row types (finite allowed words now, infinite
allowed paths later) and different fiber families can be compared by the assembly theorems.
The **prefix specialization** instantiates it with rows the allowed words and fibers chosen by
the prefix rule.

## Labels and the language

Labels are all nonempty words over a linear order `U`, admissible or not (`Label U`), so the
signature does not depend on any allowed-word membership.  The language `lang U Lc` is
relational, with equality and the symbols of `Sym U Lc`:

* `row`, arity 1: the element is a row.
* `own`, arity 2: `own(x, r)` says `x` is a fiber point whose owner row is `r`.
* `lab τ`, arity 1: the element is a fiber point with label `τ`.
* `lift R`, arity `l + 1`, for a component symbol `R : Lc.Relations (l + 1)`: all arguments lie
  in **one** fiber (same owner row, same label) and `R` holds there of their component
  elements.  Mixed-fiber tuples and row arguments are false.
* `lift0 R τ`, arity 1, for a component symbol `R : Lc.Relations 0`: `lift0 R τ (r)` says `r`
  is a row and `R` holds in the fiber of `r` at label `τ`.  This lift is **owner-indexed**: the
  nullary fact is read at the owner, so it is visible even when that fiber has no points.

**Component-language boundary.**  The assembly encodes the **relation** symbols of `Lc` only;
component function symbols are not encoded, so two component structures with the same
relational data but different function interpretations assemble identically.  For that reason
the restriction theorem that recovers component isomorphisms from an assembled isomorphism
requires `[Lc.IsRelational]`; the definitions here do not, and no unused hypothesis is imposed.

## The generic assembly

`Carrier R C` is the disjoint union of the rows and of all fiber points (`Carrier.row`,
`Carrier.pt`).  `instStructure` interprets every symbol as listed above (`relMap`), with one
interpretation equation per symbol.

## The prefix specialization

* A **row** is an allowed word: a nondecreasing list `p` over `U` with `p[i] ∈ A i` for the
  allowed sets `A : ℕ → Set U` (`IsAllowed`, `Row A`); the empty word is a row.
* The fiber of `p` at `τ` is the component `B (last τ)` if `τ` is a prefix of `p`, and the
  default component `B_*` otherwise (`compIndex`, `Comp`, `prefixFiber`).  `compIndex` is
  computable, so on concrete inputs the fiber type reduces definitionally; this is a convenience
  for regressions and claims nothing about an effective presentation of the whole assembly.
* `PrefixCarrier B_* B A := Carrier (Row A) (prefixFiber B_* B A)`.

The construction uses allowed-word membership, order comparisons, prefixes, and the component
family.  **No well-founded initial segment `W` appears anywhere.**  The input order on rows and
its successor relation are not symbols of `lang`.

The symbol set is countable when `U` and the component symbols are (`instCountableSigmaSym`).
-/

namespace FirstOrder.Language

namespace FiberAssembly

universe u v w

/-! ### Labels -/

/-- The labels: nonempty words over `U`, admissible or not. -/
def Label (U : Type u) : Type u := {τ : List U // τ ≠ []}

/-- The last letter of a label. -/
def Label.last {U : Type u} (τ : Label U) : U := τ.1.getLast τ.2

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

/-! ### The generic assembly -/

/-- The assembled carrier over a row type `R` and a fiber family `C`: rows, and the points of
every fiber. -/
inductive Carrier {U : Type u} (R : Type u) (C : R → Label U → Type u) : Type u
  | row (r : R)
  | pt (r : R) (τ : Label U) (x : C r τ)

section Generic

variable {U : Type u} {Lc : Language.{v, w}} {R : Type u} {C : R → Label U → Type u}
  [∀ r τ, Lc.Structure (C r τ)]

/-- Interpretation of each symbol, by cases on the symbol. -/
def relMap : ∀ {n : ℕ}, Sym U Lc n → (Fin n → Carrier R C) → Prop
  | _, Sym.row, v => ∃ r, v 0 = Carrier.row r
  | _, Sym.own, v => ∃ r τ x, v 0 = Carrier.pt r τ x ∧ v 1 = Carrier.row r
  | _, Sym.lab τ, v => ∃ r x, v 0 = Carrier.pt r τ x
  | _, @Sym.lift _ _ l S, v => ∃ (r : R) (τ : Label U) (y : Fin (l + 1) → C r τ),
      (∀ i, v i = Carrier.pt r τ (y i)) ∧ Structure.RelMap S y
  | _, Sym.lift0 S τ, v => ∃ r : R, v 0 = Carrier.row r ∧
      @Structure.RelMap Lc (C r τ) _ 0 S Fin.elim0

/-- The assembled structure. -/
instance instStructure : (lang U Lc).Structure (Carrier R C) where
  funMap f _ := (f : PEmpty).elim
  RelMap S v := relMap S v

/-! #### Interpretation equations, one per symbol -/

theorem relMap_row (v : Fin 1 → Carrier R C) :
    Structure.RelMap (L := lang U Lc) Sym.row v ↔ ∃ r, v 0 = Carrier.row r := Iff.rfl

theorem relMap_own (v : Fin 2 → Carrier R C) :
    Structure.RelMap (L := lang U Lc) Sym.own v ↔
      ∃ r τ x, v 0 = Carrier.pt r τ x ∧ v 1 = Carrier.row r := Iff.rfl

theorem relMap_lab (τ : Label U) (v : Fin 1 → Carrier R C) :
    Structure.RelMap (L := lang U Lc) (Sym.lab τ) v ↔ ∃ r x, v 0 = Carrier.pt r τ x := Iff.rfl

theorem relMap_lift {l : ℕ} (S : Lc.Relations (l + 1)) (v : Fin (l + 1) → Carrier R C) :
    Structure.RelMap (L := lang U Lc) (Sym.lift S) v ↔
      ∃ (r : R) (τ : Label U) (y : Fin (l + 1) → C r τ),
        (∀ i, v i = Carrier.pt r τ (y i)) ∧ Structure.RelMap S y := Iff.rfl

theorem relMap_lift0 (S : Lc.Relations 0) (τ : Label U) (v : Fin 1 → Carrier R C) :
    Structure.RelMap (L := lang U Lc) (Sym.lift0 S τ) v ↔
      ∃ r : R, v 0 = Carrier.row r ∧ @Structure.RelMap Lc (C r τ) _ 0 S Fin.elim0 := Iff.rfl

/-- Lifted relations never hold of a row argument. -/
theorem not_relMap_lift_of_row {l : ℕ} (S : Lc.Relations (l + 1)) (v : Fin (l + 1) → Carrier R C)
    (i : Fin (l + 1)) (r : R) (hv : v i = Carrier.row r) :
    ¬ Structure.RelMap (L := lang U Lc) (Sym.lift S) v := by
  rintro ⟨q, τ, y, hy, -⟩
  have := hy i
  rw [hv] at this
  cases this

/-- **Mixed-fiber tuples are false**: a lifted relation holds only of arguments from one fiber,
the same owner row and the same label. -/
theorem relMap_lift_same_fiber {l : ℕ} (S : Lc.Relations (l + 1))
    (v : Fin (l + 1) → Carrier R C) (h : Structure.RelMap (L := lang U Lc) (Sym.lift S) v)
    (i j : Fin (l + 1)) :
    ∃ (r : R) (τ : Label U) (x y : C r τ), v i = Carrier.pt r τ x ∧ v j = Carrier.pt r τ y := by
  obtain ⟨r, τ, y, hy, -⟩ := h
  exact ⟨r, τ, y i, y j, hy i, hy j⟩

/-- The lift of a nullary symbol is read at the owner row; it does not require the fiber to
have any point. -/
theorem relMap_lift0_row (S : Lc.Relations 0) (τ : Label U) (r : R) :
    Structure.RelMap (L := lang U Lc) (Sym.lift0 S τ)
      (fun _ : Fin 1 => (Carrier.row r : Carrier R C)) ↔
      @Structure.RelMap Lc (C r τ) _ 0 S Fin.elim0 := by
  constructor
  · rintro ⟨r', hr, h⟩
    cases hr
    exact h
  · intro h
    exact ⟨r, rfl, h⟩

end Generic

/-! ### The prefix specialization -/

/-- An allowed word: nondecreasing, with the `i`-th letter in `A i`. -/
def IsAllowed {U : Type u} [LinearOrder U] (A : ℕ → Set U) (p : List U) : Prop :=
  p.Pairwise (· ≤ ·) ∧ ∀ (i : ℕ) (h : i < p.length), p[i] ∈ A i

theorem isAllowed_nil {U : Type u} [LinearOrder U] (A : ℕ → Set U) : IsAllowed A [] :=
  ⟨List.Pairwise.nil, fun i h => absurd h (Nat.not_lt_zero i)⟩

/-- The rows of the prefix specialization: allowed words, the empty word included. -/
def Row {U : Type u} [LinearOrder U] (A : ℕ → Set U) : Type u := {p : List U // IsAllowed A p}

/-- Which component sits at `(p, τ)`: `some (last τ)` if `τ` is a prefix of `p`, else `none`
(the default component).  Computable, so it reduces on concrete inputs. -/
def compIndex {U : Type u} [DecidableEq U] (p : List U) (τ : Label U) : Option U :=
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

/-- The prefix fiber family: the component of `last τ` when `τ` is a prefix of the row, the
default component otherwise. -/
def prefixFiber {U : Type u} [LinearOrder U] (Bstar : Type u) (B : U → Type u)
    (A : ℕ → Set U) : Row A → Label U → Type u :=
  fun p τ => Comp Bstar B (compIndex p.1 τ)

instance instPrefixFiberStructure {U : Type u} [LinearOrder U] (Lc : Language.{v, w})
    (Bstar : Type u) (B : U → Type u) (A : ℕ → Set U)
    [Lc.Structure Bstar] [∀ u, Lc.Structure (B u)] :
    ∀ (p : Row A) (τ : Label U), Lc.Structure (prefixFiber Bstar B A p τ) :=
  fun p τ => instCompStructure Lc Bstar B (compIndex p.1 τ)

/-- The carrier of the prefix specialization. -/
abbrev PrefixCarrier {U : Type u} [LinearOrder U] (Bstar : Type u) (B : U → Type u)
    (A : ℕ → Set U) : Type u :=
  Carrier (Row A) (prefixFiber Bstar B A)

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
      | ⟨_, @Sym.lift _ _ l S⟩ => Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨l + 1, S⟩)))
      | ⟨_, Sym.lift0 S τ⟩ => Sum.inr (Sum.inr (Sum.inr (Sum.inr (⟨0, S⟩, τ))))
  have : Countable (Label U) := Subtype.countable
  refine Function.Injective.countable (f := code) ?_
  rintro ⟨n₁, s₁⟩ ⟨n₂, s₂⟩ h
  cases s₁ <;> cases s₂ <;> simp only [code, Sum.inl.injEq, Sum.inr.injEq, Sigma.mk.injEq,
    Prod.mk.injEq, reduceCtorEq] at h
  · rfl
  · rfl
  · subst h; rfl
  · obtain ⟨hl, hS⟩ := h
    have := Nat.succ_injective hl
    subst this
    cases hS
    rfl
  · obtain ⟨⟨-, hS⟩, hτ⟩ := h
    cases hS; subst hτ; rfl

end FiberAssembly

end FirstOrder.Language
