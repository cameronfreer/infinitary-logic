/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.FiberAssembly

/-!
# Companion carriers: allowed paths, prefixes, and the path row

The **companion** of the prefix specialization along an infinite allowed path `π` is the generic
carrier over the rows `Row A ⊕ Unit`: the finite allowed rows keep their fibers, and the extra
row `ρ_π` follows the same prefix rule along `π` (`pathFiber`, `CompanionCarrier`).

* `IsAllowedPath A π`: `π` is nondecreasing with `π n ∈ A n`.  Allowedness is a **hypothesis**
  where a prefix must be a row; the constructor does not bake in approximation or
  non-defaultness of the components along the path.
* `pathPrefix π k`: the prefix `[π 0, …, π (k - 1)]`; `prefixRow hπ k` is it as an allowed row.
  Prefixes of different lengths are distinct.
* `IsPathPrefix π τ`: a label lies on the path; `pathIndex π τ` is `some (last τ)` then and
  `none` otherwise.
* **Fiber-index equations**: `compIndex (pathPrefix π k) τ = pathIndex π τ` for labels of
  length `≤ k` and `= none` for longer labels (`compIndex_pathPrefix_of_le`,
  `compIndex_pathPrefix_of_lt`); consecutive prefixes differ only at the label of length
  `k + 1` (`compIndex_pathPrefix_succ_of_ne`), where the longer prefix gives `some (π k)` and the
  shorter gives `none`.  Hence `ρ_π` and `π|ₖ` have equal fibers at every label of length `≤ k`
  (`pathFiber_inl_prefixRow_of_le`).
* Countability of the companion carrier from countable letters, default, and components.

Nothing about equivalence, isomorphism, or ranks is proved here.
-/

namespace FirstOrder.Language

namespace FiberAssembly

universe u v w

/-! ### Prefixes of a path (no order structure needed) -/

section Prefixes

variable {U : Type u}

/-- The prefix `[π 0, …, π (k - 1)]` of a path. -/
def pathPrefix (π : ℕ → U) (k : ℕ) : List U := List.ofFn fun i : Fin k => π i

@[simp] theorem pathPrefix_length (π : ℕ → U) (k : ℕ) : (pathPrefix π k).length = k :=
  List.length_ofFn

@[simp] theorem pathPrefix_zero (π : ℕ → U) : pathPrefix π 0 = [] := by
  simp [pathPrefix]

theorem pathPrefix_succ (π : ℕ → U) (k : ℕ) :
    pathPrefix π (k + 1) = pathPrefix π k ++ [π k] := by
  simp only [pathPrefix, List.ofFn_succ', List.concat_eq_append, Fin.val_castSucc, Fin.val_last]

@[simp] theorem pathPrefix_getElem (π : ℕ → U) (k : ℕ) (i : ℕ) (h : i < (pathPrefix π k).length) :
    (pathPrefix π k)[i] = π i := by
  simp [pathPrefix]

theorem pathPrefix_ne_nil (π : ℕ → U) (k : ℕ) : pathPrefix π (k + 1) ≠ [] := by
  intro h
  have := congrArg List.length h
  simp at this

/-- A shorter prefix is a prefix of a longer one. -/
theorem pathPrefix_prefix (π : ℕ → U) {j k : ℕ} (h : j ≤ k) :
    pathPrefix π j <+: pathPrefix π k := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp [pathPrefix]

/-- A list that is a prefix of `pathPrefix π k` is the prefix of its own length. -/
theorem eq_pathPrefix_of_prefix (π : ℕ → U) {l : List U} {k : ℕ} (h : l <+: pathPrefix π k) :
    l = pathPrefix π l.length := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [h.getElem h1, pathPrefix_getElem, pathPrefix_getElem]

/-! ### Labels on the path -/

/-- A label lies on the path: it is the path prefix of its own length. -/
def IsPathPrefix (π : ℕ → U) (τ : Label U) : Prop := τ.1 = pathPrefix π τ.1.length

instance [DecidableEq U] (π : ℕ → U) (τ : Label U) : Decidable (IsPathPrefix π τ) :=
  inferInstanceAs (Decidable (τ.1 = pathPrefix π τ.1.length))

/-- For labels no longer than `k`, lying on the path is being a prefix of `π|ₖ`. -/
theorem isPathPrefix_iff_prefix {π : ℕ → U} {τ : Label U} {k : ℕ} (h : τ.1.length ≤ k) :
    IsPathPrefix π τ ↔ τ.1 <+: pathPrefix π k := by
  constructor
  · intro hτ
    rw [IsPathPrefix] at hτ
    rw [hτ]
    exact pathPrefix_prefix π h
  · intro hτ
    exact eq_pathPrefix_of_prefix π hτ

/-- A label longer than `k` is not a prefix of `π|ₖ`. -/
theorem not_prefix_pathPrefix_of_lt {π : ℕ → U} {τ : Label U} {k : ℕ} (h : k < τ.1.length) :
    ¬ τ.1 <+: pathPrefix π k := by
  intro hτ
  have := hτ.length_le
  simp only [pathPrefix_length] at this
  omega

/-- The prefix of length `k + 1`, as a label. -/
def prefixLabel (π : ℕ → U) (k : ℕ) : Label U := ⟨pathPrefix π (k + 1), pathPrefix_ne_nil π k⟩

@[simp] theorem prefixLabel_val (π : ℕ → U) (k : ℕ) :
    (prefixLabel π k).1 = pathPrefix π (k + 1) := rfl

theorem prefixLabel_last (π : ℕ → U) (k : ℕ) : (prefixLabel π k).last = π k := by
  unfold Label.last
  rw [List.getLast_eq_getElem]
  simp

theorem isPathPrefix_prefixLabel (π : ℕ → U) (k : ℕ) : IsPathPrefix π (prefixLabel π k) := by
  unfold IsPathPrefix
  simp

section Index

variable [DecidableEq U]

/-- The component index along the path: `some (last τ)` on the path, `none` off it. -/
def pathIndex (π : ℕ → U) (τ : Label U) : Option U :=
  if IsPathPrefix π τ then some τ.last else none

theorem pathIndex_of_isPathPrefix {π : ℕ → U} {τ : Label U} (h : IsPathPrefix π τ) :
    pathIndex π τ = some τ.last := by
  unfold pathIndex
  simp [h]

theorem pathIndex_of_not_isPathPrefix {π : ℕ → U} {τ : Label U} (h : ¬ IsPathPrefix π τ) :
    pathIndex π τ = none := by
  unfold pathIndex
  simp [h]

theorem pathIndex_prefixLabel (π : ℕ → U) (k : ℕ) : pathIndex π (prefixLabel π k) = some (π k) := by
  rw [pathIndex_of_isPathPrefix (isPathPrefix_prefixLabel π k), prefixLabel_last]

/-! ### Fiber-index equations -/

/-- **Short labels**: the prefix row `π|ₖ` indexes a label of length `≤ k` exactly as the path
does. -/
theorem compIndex_pathPrefix_of_le {π : ℕ → U} {τ : Label U} {k : ℕ} (h : τ.1.length ≤ k) :
    compIndex (pathPrefix π k) τ = pathIndex π τ := by
  by_cases hτ : IsPathPrefix π τ
  · rw [compIndex_of_prefix ((isPathPrefix_iff_prefix h).mp hτ), pathIndex_of_isPathPrefix hτ]
  · rw [compIndex_of_not_prefix (fun h' => hτ ((isPathPrefix_iff_prefix h).mpr h')),
      pathIndex_of_not_isPathPrefix hτ]

/-- **Long labels**: the prefix row `π|ₖ` gives the default at every label longer than `k`. -/
theorem compIndex_pathPrefix_of_lt {π : ℕ → U} {τ : Label U} {k : ℕ} (h : k < τ.1.length) :
    compIndex (pathPrefix π k) τ = none :=
  compIndex_of_not_prefix (not_prefix_pathPrefix_of_lt h)

/-- **Consecutive prefixes** differ only at the label of length `k + 1`. -/
theorem compIndex_pathPrefix_succ_of_ne {π : ℕ → U} {τ : Label U} {k : ℕ}
    (h : τ.1.length ≠ k + 1) :
    compIndex (pathPrefix π (k + 1)) τ = compIndex (pathPrefix π k) τ := by
  rcases Nat.lt_or_ge k τ.1.length with hk | hk
  · have hk' : k + 1 < τ.1.length := by omega
    rw [compIndex_pathPrefix_of_lt hk, compIndex_pathPrefix_of_lt hk']
  · rw [compIndex_pathPrefix_of_le hk, compIndex_pathPrefix_of_le (Nat.le_succ_of_le hk)]

/-- At the label of length `k + 1` on the path, the longer prefix gives `some (π k)`. -/
theorem compIndex_pathPrefix_succ_prefixLabel (π : ℕ → U) (k : ℕ) :
    compIndex (pathPrefix π (k + 1)) (prefixLabel π k) = some (π k) := by
  rw [compIndex_pathPrefix_of_le (by simp), pathIndex_prefixLabel]

/-- At the label of length `k + 1` on the path, the shorter prefix gives the default. -/
theorem compIndex_pathPrefix_prefixLabel (π : ℕ → U) (k : ℕ) :
    compIndex (pathPrefix π k) (prefixLabel π k) = none :=
  compIndex_pathPrefix_of_lt (by simp)

end Index

end Prefixes

/-! ### Allowed paths and prefix rows -/

variable {U : Type u} [LinearOrder U]

/-- An allowed path: nondecreasing, with the `n`-th letter allowed at position `n`. -/
def IsAllowedPath (A : ℕ → Set U) (π : ℕ → U) : Prop :=
  Monotone π ∧ ∀ n, π n ∈ A n

/-- Prefixes of an allowed path are allowed rows. -/
theorem isAllowed_pathPrefix {A : ℕ → Set U} {π : ℕ → U} (hπ : IsAllowedPath A π) (k : ℕ) :
    IsAllowed A (pathPrefix π k) := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [pathPrefix, List.pairwise_ofFn]
    intro i j hij
    exact hπ.1 (le_of_lt hij)
  · rw [pathPrefix_getElem]
    exact hπ.2 i

/-- The prefix of length `k` as an allowed row. -/
def prefixRow {A : ℕ → Set U} {π : ℕ → U} (hπ : IsAllowedPath A π) (k : ℕ) : Row A :=
  ⟨pathPrefix π k, isAllowed_pathPrefix hπ k⟩

@[simp] theorem prefixRow_val {A : ℕ → Set U} {π : ℕ → U} (hπ : IsAllowedPath A π) (k : ℕ) :
    (prefixRow hπ k).1 = pathPrefix π k := rfl

/-- Prefixes of different lengths are different rows. -/
theorem prefixRow_injective {A : ℕ → Set U} {π : ℕ → U} (hπ : IsAllowedPath A π) :
    Function.Injective (prefixRow hπ) := by
  intro j k h
  have := congrArg (fun p : Row A => p.1.length) h
  simpa using this

/-! ### The companion carrier -/

variable {Lc : Language.{v, w}} (Bstar : Type u) (B : U → Type u) (A : ℕ → Set U) (π : ℕ → U)

/-- The fibers of the companion: finite rows as in the base, the path row by the prefix rule
along `π`. -/
def pathFiber : (Row A ⊕ Unit) → Label U → Type u
  | Sum.inl r, τ => prefixFiber Bstar B A r τ
  | Sum.inr _, τ => Comp Bstar B (pathIndex π τ)

@[simp] theorem pathFiber_inl (r : Row A) (τ : Label U) :
    pathFiber Bstar B A π (Sum.inl r) τ = prefixFiber Bstar B A r τ := rfl

@[simp] theorem pathFiber_inr (τ : Label U) :
    pathFiber Bstar B A π (Sum.inr ()) τ = Comp Bstar B (pathIndex π τ) := rfl

instance instPathFiberStructure [Lc.Structure Bstar] [∀ u, Lc.Structure (B u)] :
    ∀ (r : Row A ⊕ Unit) (τ : Label U), Lc.Structure (pathFiber Bstar B A π r τ)
  | Sum.inl r, τ => instPrefixFiberStructure Lc Bstar B A r τ
  | Sum.inr _, τ => instCompStructure Lc Bstar B (pathIndex π τ)

/-- The companion carrier along `π`. -/
abbrev CompanionCarrier : Type u := Carrier (Row A ⊕ Unit) (pathFiber Bstar B A π)

/-- The path row and a prefix row `π|ₖ` have the same fiber at every label of length `≤ k`. -/
theorem pathFiber_inl_prefixRow_of_le {hπ : IsAllowedPath A π} {k : ℕ} {τ : Label U}
    (h : τ.1.length ≤ k) :
    pathFiber Bstar B A π (Sum.inl (prefixRow hπ k)) τ = pathFiber Bstar B A π (Sum.inr ()) τ := by
  show Comp Bstar B (compIndex (pathPrefix π k) τ) = Comp Bstar B (pathIndex π τ)
  rw [compIndex_pathPrefix_of_le h]

/-- The companion carrier is countable when the letters, the default, and the components are. -/
instance instCountableCompanion [Countable U] [Countable Bstar] [∀ u, Countable (B u)] :
    Countable (CompanionCarrier Bstar B A π) := by
  have : ∀ (r : Row A ⊕ Unit) (τ : Label U), Countable (pathFiber Bstar B A π r τ) := by
    rintro (r | _) τ
    · exact instCountablePrefixFiber Bstar B A r τ
    · exact instCountableComp Bstar B _
  exact instCountableCarrier _ _

end FiberAssembly

end FirstOrder.Language
