/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.SkolemClosure

/-!
# Ehrenfeucht–Mostowski term model (M-deep-interpretation), step 1: skeleton support

The bespoke EM term model realizes the tail-template theory over `(skolemColim L)[[J]]` without
full compactness. Its carrier is the closed terms quotiented by **deep equality in the source model
`M`**: two closed terms are identified when, interpreting their finitely-many `J`-constants as a
strictly-increasing *deep* tuple of the tail-indiscernible sequence, they evaluate equally in `M`
(eventually, as the depth grows). Congruence is then inherited from `M` being a genuine structure.

This file builds the first ingredient: the finite set of `J`-constants ("skeleton constants")
mentioned in a closed term, which the deep interpretation enumerates in increasing `J`-order.
-/

namespace FirstOrder.Language

variable (L : Language.{0, 0}) (J : Type) [LinearOrder J]

/-- The `J`-constant carried by a function symbol of `(skolemColim L)[[J]]`: only an arity-`0`
symbol from the `constantsOn J` summand is a skeleton constant. -/
def jConstOf : {n : ℕ} → (skolemColim L)[[J]].Functions n → Finset J
  | 0, Sum.inr j => {j}
  | _, _ => ∅

/-- The finite set of `J`-constants (skeleton constants) mentioned in a term of
`(skolemColim L)[[J]]`. The deep interpretation enumerates this support in increasing `J`-order. -/
def jSupport {α : Type} : (skolemColim L)[[J]].Term α → Finset J
  | .var _ => ∅
  | .func f ts => (Finset.univ.biUnion fun i => jSupport (ts i)) ∪ jConstOf L J f

/-- Support monotonicity: an argument's skeleton support is contained in the whole term's. -/
theorem jSupport_subterm {α : Type} {n : ℕ} (f : (skolemColim L)[[J]].Functions n)
    (ts : Fin n → (skolemColim L)[[J]].Term α) (i : Fin n) :
    jSupport L J (ts i) ⊆ jSupport L J (.func f ts) := fun _ hx =>
  Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)

/-! ### Step 2: ordered support (ranks) -/

/-- The **rank** of `j` in a finite support `S`: the number of support elements below it, i.e. its
0-indexed position in the increasing `J`-order. So a support `{j₀ < j₁ < …}` has ranks `0, 1, …`
and the deep interpretation sends it to `a_d, a_{d+1}, …` (a strictly-increasing deep tuple). -/
def deepRank (S : Finset J) (j : J) : ℕ := (S.filter (· < j)).card

/-- On the support, ranks strictly increase with `J`-order: the deep tuple is strictly increasing,
hence injective on the support. -/
theorem deepRank_lt_of_lt {S : Finset J} {j j' : J} (hj : j ∈ S) (hjj' : j < j') :
    deepRank J S j < deepRank J S j' := by
  apply Finset.card_lt_card
  refine ⟨fun x hx => ?_, fun hsub => ?_⟩
  · rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_trans hx.2 hjj'⟩
  · exact absurd (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hj, hjj'⟩))).2 (lt_irrefl j)

/-! ### Step 3: deep interpretation -/

section DeepInterp

variable {M : Type} [L.Structure M] [Nonempty M] (a : ℕ → M)

/-- The **deep interpretation** of a closed term at depth `d` relative to a support `S`: interpret
each `J`-constant `c_j` by the source sequence at position `d + deepRank S j` (so support constants
map to a strictly-increasing deep tuple of `a`), and evaluate in `M`'s `L^Sk`-structure. -/
noncomputable def deepInterp (d : ℕ) (S : Finset J) (t : (skolemColim L)[[J]].Term Empty) : M :=
  letI : (skolemColim L).Structure M := skolemColimStructure L
  letI : (constantsOn J).Structure M := constantsOn.structure (fun j => a (d + deepRank J S j))
  t.realize Empty.elim

/-- Deep interpretation commutes with function application (same depth and support): it is the
structure's `funMap` of the argument interpretations. Immediate from `Term.realize`. -/
theorem deepInterp_func (d : ℕ) (S : Finset J) {n : ℕ}
    (f : (skolemColim L)[[J]].Functions n) (ts : Fin n → (skolemColim L)[[J]].Term Empty) :
    deepInterp L J a d S (.func f ts) =
      letI : (skolemColim L).Structure M := skolemColimStructure L
      letI : (constantsOn J).Structure M := constantsOn.structure (fun j => a (d + deepRank J S j))
      Structure.funMap f (fun i => deepInterp L J a d S (ts i)) :=
  rfl

/-- Shifting the depth past a cutoff sends every support constant past it: each constant lands at
position `≥ d`, so `N ≤ d` forces all positions `≥ N`. -/
theorem le_depth_position (d : ℕ) (S : Finset J) (j : J) : d ≤ d + deepRank J S j :=
  Nat.le_add_right _ _

end DeepInterp

end FirstOrder.Language
