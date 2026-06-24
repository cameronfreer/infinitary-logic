/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.SkolemClosure
import InfinitaryLogic.Methods.EM.TailAdapter
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

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

/-- The variables of a relabeled term are the image of the original variables (a Mathlib gap). -/
theorem Term.varFinset_relabel {L' : Language} {α β : Type} [DecidableEq α] [DecidableEq β]
    (g : α → β) (t : L'.Term α) : (t.relabel g).varFinset = t.varFinset.image g := by
  induction t with
  | var i => simp [Term.relabel, Term.varFinset]
  | func f ts ih =>
    ext x
    simp only [Term.relabel, Term.varFinset, ih, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image]
    tauto

/-- A term's realization depends only on the assignment of the variables that actually appear (a
Mathlib gap). -/
theorem Term.realize_eq_of_eq_on_varFinset {L' : Language} {M' : Type} [L'.Structure M']
    {α : Type} [DecidableEq α] {v w : α → M'} :
    ∀ t : L'.Term α, (∀ x ∈ t.varFinset, v x = w x) → t.realize v = t.realize w := by
  intro t
  induction t with
  | var i => intro h; exact h i (by simp [Term.varFinset])
  | func f ts ih =>
    intro h
    simp only [Term.realize]
    congr 1
    funext i
    exact ih i (fun x hx => h x (by
      simp only [Term.varFinset, Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ i, hx⟩))

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

/-- The de-substituted term `constantsToVars t` uses only the variables `Sum.inl j` for `j` a
skeleton constant of `t`: its variable set is contained in `Sum.inl` of the skeleton support. -/
theorem constantsToVars_varFinset_subset (t : (skolemColim L)[[J]].Term Empty) :
    t.constantsToVars.varFinset ⊆ (jSupport L J t).image Sum.inl := by
  induction t with
  | var e => exact e.elim
  | @func l f ts ih =>
    rcases l with _ | l
    · rcases f with f' | c
      · simp [Term.constantsToVars, Term.varFinset]
      · simp [Term.constantsToVars, jSupport, jConstOf, Term.varFinset]
    · rcases f with f' | c
      · simp only [Term.constantsToVars, Term.varFinset, jSupport, jConstOf, Finset.union_empty]
        intro x hx
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
        obtain ⟨i, hxi⟩ := hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (ih i hxi)
        exact Finset.mem_image.mpr ⟨y, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hy⟩, rfl⟩
      · exact c.elim

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

/-- The rank of the `i`-th support element (in increasing order) is `i`: the enumeration
`orderEmbOfFin` and the rank are mutually inverse. The elements of `S` strictly below the `i`-th
are exactly the first `i`. -/
theorem deepRank_orderEmbOfFin (S : Finset J) {k : ℕ} (h : S.card = k) (i : Fin k) :
    deepRank J S (S.orderEmbOfFin h i) = (i : ℕ) := by
  have step : S.filter (· < S.orderEmbOfFin h i)
      = (Finset.univ.filter (fun j : Fin k => j < i)).image (S.orderEmbOfFin h) := by
    conv_lhs => arg 2; rw [← Finset.image_orderEmbOfFin_univ S h]
    rw [Finset.filter_image]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, OrderEmbedding.lt_iff_lt]
  unfold deepRank
  rw [step, Finset.card_image_of_injective _ (S.orderEmbOfFin h).injective,
    Finset.filter_gt_eq_Iio, Fin.card_Iio]

/-- The rank of a support element is below the cardinality: a valid `Fin S.card` position. -/
theorem deepRank_lt_card {S : Finset J} {j : J} (hj : j ∈ S) : deepRank J S j < S.card := by
  have hmem : (j : J) ∈ Set.range (S.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin S rfl]; exact hj
  obtain ⟨i, rfl⟩ := hmem
  rw [deepRank_orderEmbOfFin]; exact i.2

/-- The enumeration recovers a support element from its rank: `orderEmbOfFin` at position
`deepRank S j` is `j`, for `j ∈ S`. -/
theorem orderEmbOfFin_deepRank (S : Finset J) {k : ℕ} (h : S.card = k) {j : J} (hj : j ∈ S)
    (hlt : deepRank J S j < k) : S.orderEmbOfFin h ⟨deepRank J S j, hlt⟩ = j := by
  have hmem : (j : J) ∈ Set.range (S.orderEmbOfFin h) := by
    rw [Finset.range_orderEmbOfFin S h]; exact hj
  obtain ⟨i, rfl⟩ := hmem
  congr 1
  exact Fin.ext (deepRank_orderEmbOfFin J S h i)

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

/-- **De-substitution bridge** (step 2): the deep interpretation of a closed term equals the
*de-substituted* `L^Sk`-term `constantsToVars t` (each skeleton constant `c_j` turned into the
variable `Sum.inl j`) realized with `j ↦ a (d + deepRank S j)`. Turns the support machinery from
combinatorial into semantic — the right-hand side is a genuine formula realization, so tail
indiscernibility applies. -/
theorem deepInterp_eq_realize (d : ℕ) (S : Finset J) (t : (skolemColim L)[[J]].Term Empty) :
    letI : (skolemColim L).Structure M := skolemColimStructure L
    deepInterp L J a d S t =
      t.constantsToVars.realize (Sum.elim (fun j => a (d + deepRank J S j)) Empty.elim) := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  letI : (constantsOn J).Structure M := constantsOn.structure (fun j => a (d + deepRank J S j))
  show t.realize Empty.elim = _
  exact (Term.realize_constantsToVars (t := t) (v := Empty.elim)).symm

/-- The **de-substituted term at ordered support positions**: each skeleton constant `c_j` becomes
the `ℕ`-variable `deepRank S j` (its 0-indexed position in the increasing support order). An
`L^Sk`-term over `ℕ`. (Over `ℕ` rather than `Fin S.card` so the relabel needs no junk value; only
the values `< S.card` are hit when `jSupport t ⊆ S`.) -/
def deTermPos (S : Finset J) (t : (skolemColim L)[[J]].Term Empty) : (skolemColim L).Term ℕ :=
  t.constantsToVars.relabel (Sum.elim (fun j => deepRank J S j) Empty.elim)

/-- The ordered-position term uses only variables `< S.card` (valid `Fin S.card` positions), once the
support `S` covers the term's skeleton constants. -/
theorem deTermPos_varFinset_subset {S : Finset J} {t : (skolemColim L)[[J]].Term Empty}
    (hsub : jSupport L J t ⊆ S) : (deTermPos L J S t).varFinset ⊆ Finset.range S.card := by
  rw [deTermPos, Term.varFinset_relabel]
  intro n hn
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (constantsToVars_varFinset_subset L J t hx)
  simp only [Sum.elim_inl]
  exact Finset.mem_range.mpr (deepRank_lt_card (J := J) (hsub hj))

/-- **Ordered-position realize bridge** (step 3): the deep interpretation is the realize of the
ordered-position de-substituted term on the *consecutive* deep tuple `n ↦ a (d + n)`. The cleaned-up
form of `deepInterp_eq_realize`, with variables at ordered support positions — exactly the shape tail
indiscernibility consumes (a strictly-increasing deep tuple). -/
theorem deepInterp_eq_realize_pos (d : ℕ) (S : Finset J) (t : (skolemColim L)[[J]].Term Empty) :
    letI : (skolemColim L).Structure M := skolemColimStructure L
    deepInterp L J a d S t = (deTermPos L J S t).realize (fun n => a (d + n)) := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  rw [deepInterp_eq_realize, deTermPos, Term.realize_relabel]
  congr 1
  funext x
  cases x with
  | inl j => rfl
  | inr e => exact e.elim

/-- The **de-substituted term at `Fin S.card` positions**: `deTermPos` with its (already `< S.card`)
variables packaged as genuine `Fin S.card` indices, via `restrictVar` (no junk value needed, since
every variable that appears is `< S.card` when `S` covers the skeleton constants). The arity-`S.card`
term whose equality atom tail indiscernibility consumes. -/
def deTermFin (S : Finset J) (t : (skolemColim L)[[J]].Term Empty) (hsub : jSupport L J t ⊆ S) :
    (skolemColim L).Term (Fin S.card) :=
  (deTermPos L J S t).restrictVar
    (fun x => ⟨x.1, Finset.mem_range.mp (deTermPos_varFinset_subset (L := L) (J := J) hsub x.2)⟩)

/-- **`Fin`-arity realize bridge**: the deep interpretation is the realize of the `Fin S.card`-indexed
de-substituted term on the consecutive deep tuple `i ↦ a (d + i)`. The `Fin`-arity form of
`deepInterp_eq_realize_pos`, directly feeding the atom. -/
theorem deepInterp_eq_realize_fin (d : ℕ) (S : Finset J) (t : (skolemColim L)[[J]].Term Empty)
    (hsub : jSupport L J t ⊆ S) :
    letI : (skolemColim L).Structure M := skolemColimStructure L
    deepInterp L J a d S t = (deTermFin L J S t hsub).realize (fun i : Fin S.card => a (d + i)) := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  rw [deepInterp_eq_realize_pos, deTermFin]
  symm
  exact Term.realize_restrictVar (fun n => a (d + n)) (fun _ => rfl)

/-- **Per-term superset realize**: the `Fin`-arity de-substituted term over `S`, realized on the
`T`-induced deep tuple `i ↦ a (d + deepRank T (orderEmbOfFin S i))`, equals the deep interpretation
over the larger support `T`. The core shared by the equality- and relation-atom superset bridges
(restrictVar realize with a `dite`-extended assignment, then `realize_eq_of_eq_on_varFinset` to
discard the junk, then `orderEmbOfFin_deepRank`). -/
theorem deTermFin_realize_superset (d : ℕ) (S T : Finset J) (w : (skolemColim L)[[J]].Term Empty)
    (hw : jSupport L J w ⊆ S) :
    letI : (skolemColim L).Structure M := skolemColimStructure L
    (deTermFin L J S w hw).realize
        (fun i : Fin S.card => a (d + deepRank J T (S.orderEmbOfFin rfl i)))
      = deepInterp L J a d T w := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  have hrv : (deTermFin L J S w hw).realize
        (fun i : Fin S.card => a (d + deepRank J T (S.orderEmbOfFin rfl i)))
      = (deTermPos L J S w).realize
        (fun n => a (d + if h : n < S.card then deepRank J T (S.orderEmbOfFin rfl ⟨n, h⟩) else 0)) := by
    rw [deTermFin]
    refine Term.realize_restrictVar
      (fun n => a (d + if h : n < S.card then deepRank J T (S.orderEmbOfFin rfl ⟨n, h⟩) else 0))
      (fun x => ?_)
    simp only [dif_pos (Finset.mem_range.mp (deTermPos_varFinset_subset (L := L) (J := J) hw x.2))]
  rw [hrv, deepInterp_eq_realize, deTermPos, Term.realize_relabel]
  apply Term.realize_eq_of_eq_on_varFinset
  intro x hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (constantsToVars_varFinset_subset L J w hx)
  have hjS : j ∈ S := hw hj
  have hlt : deepRank J S j < S.card := deepRank_lt_card (J := J) hjS
  simp only [Function.comp_apply, Sum.elim_inl, dif_pos hlt]
  rw [orderEmbOfFin_deepRank J S rfl hjS hlt]

/-- The **de-substituted equality atom** of two closed terms over a covering support `S`: an
`L^Sk`-formula of arity `S.card` whose truth on the consecutive deep tuple is the deep equality of
`t, u`. Since `L^Sk` is countable, all such atoms form a countable family that seeds the
tail-indiscernible `Γ`. -/
def deEqAtom (S : Finset J) (t u : (skolemColim L)[[J]].Term Empty)
    (ht : jSupport L J t ⊆ S) (hu : jSupport L J u ⊆ S) :
    (skolemColim L).BoundedFormulaω Empty S.card :=
  BoundedFormulaω.equal ((deTermFin L J S t ht).relabel Sum.inr)
    ((deTermFin L J S u hu).relabel Sum.inr)

/-- **Atom realize bridge** (step 4): the de-substituted equality atom holds on the consecutive deep
tuple `i ↦ a (d + i)` iff `t` and `u` have equal deep interpretations at depth `d` over `S`. -/
theorem realize_deEqAtom (d : ℕ) (S : Finset J) (t u : (skolemColim L)[[J]].Term Empty)
    (ht : jSupport L J t ⊆ S) (hu : jSupport L J u ⊆ S) :
    letI : (skolemColim L).Structure M := skolemColimStructure L
    (deEqAtom L J S t u ht hu).Realize Empty.elim (fun i : Fin S.card => a (d + i)) ↔
      deepInterp L J a d S t = deepInterp L J a d S u := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  rw [deEqAtom, BoundedFormulaω.realize_equal, Term.realize_relabel, Term.realize_relabel,
    Sum.elim_comp_inr, ← deepInterp_eq_realize_fin (t := t) (hsub := ht),
    ← deepInterp_eq_realize_fin (t := u) (hsub := hu)]

/-- **Superset atom bridge** (step 5, renaming): the *same* equality atom over `S`, realized on the
`T`-induced deep tuple `i ↦ a (d + deepRank T (orderEmbOfFin S i))` (where `S ⊆ T`), holds iff `t` and
`u` have equal deep interpretations over the larger support `T`. So one arity-`S.card` formula carries
both the `S`-truth (on the consecutive tuple) and the `T`-truth (on this strictly-increasing tuple) —
the input to tail indiscernibility. -/
theorem realize_deEqAtom_superset (d : ℕ) {S T : Finset J} (_hST : S ⊆ T)
    (t u : (skolemColim L)[[J]].Term Empty)
    (ht : jSupport L J t ⊆ S) (hu : jSupport L J u ⊆ S) :
    letI : (skolemColim L).Structure M := skolemColimStructure L
    (deEqAtom L J S t u ht hu).Realize Empty.elim
        (fun i : Fin S.card => a (d + deepRank J T (S.orderEmbOfFin rfl i))) ↔
      deepInterp L J a d T t = deepInterp L J a d T u := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  have key : ∀ (w : (skolemColim L)[[J]].Term Empty) (hw : jSupport L J w ⊆ S),
      (deTermFin L J S w hw).realize
          (fun i : Fin S.card => a (d + deepRank J T (S.orderEmbOfFin rfl i)))
        = deepInterp L J a d T w := by
    intro w hw
    have hrv : (deTermFin L J S w hw).realize
          (fun i : Fin S.card => a (d + deepRank J T (S.orderEmbOfFin rfl i)))
        = (deTermPos L J S w).realize
          (fun n => a (d + if h : n < S.card then deepRank J T (S.orderEmbOfFin rfl ⟨n, h⟩) else 0)) := by
      rw [deTermFin]
      refine Term.realize_restrictVar
        (fun n => a (d + if h : n < S.card then deepRank J T (S.orderEmbOfFin rfl ⟨n, h⟩) else 0))
        (fun x => ?_)
      simp only [dif_pos (Finset.mem_range.mp (deTermPos_varFinset_subset (L := L) (J := J) hw x.2))]
    rw [hrv, deepInterp_eq_realize, deTermPos, Term.realize_relabel]
    apply Term.realize_eq_of_eq_on_varFinset
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (constantsToVars_varFinset_subset L J w hx)
    have hjS : j ∈ S := hw hj
    have hlt : deepRank J S j < S.card := deepRank_lt_card (J := J) hjS
    simp only [Function.comp_apply, Sum.elim_inl, dif_pos hlt]
    rw [orderEmbOfFin_deepRank J S rfl hjS hlt]
  rw [deEqAtom, BoundedFormulaω.realize_equal, Term.realize_relabel, Term.realize_relabel,
    Sum.elim_comp_inr, key t ht, key u hu]

/-- The **de-substituted relation atom**: the relation `R` applied to the `Fin`-arity de-substituted
terms of a tuple over a covering support `S`. The relation analogue of `deEqAtom`. -/
def deRelAtom (S : Finset J) {l : ℕ} (R : (skolemColim L).Relations l)
    (ts : Fin l → (skolemColim L)[[J]].Term Empty) (ht : ∀ i, jSupport L J (ts i) ⊆ S) :
    (skolemColim L).BoundedFormulaω Empty S.card :=
  BoundedFormulaω.rel R fun i => (deTermFin L J S (ts i) (ht i)).relabel Sum.inr

/-- **Relation atom realize bridge**: the de-substituted relation atom holds on the consecutive deep
tuple iff `R` holds in `M` on the deep interpretations over `S`. -/
theorem realize_deRelAtom (d : ℕ) (S : Finset J) {l : ℕ} (R : (skolemColim L).Relations l)
    (ts : Fin l → (skolemColim L)[[J]].Term Empty) (ht : ∀ i, jSupport L J (ts i) ⊆ S) :
    letI : (skolemColim L).Structure M := skolemColimStructure L
    (deRelAtom L J S R ts ht).Realize Empty.elim (fun i : Fin S.card => a (d + i)) ↔
      Structure.RelMap R fun i => deepInterp L J a d S (ts i) := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  rw [deRelAtom, BoundedFormulaω.realize_rel]
  apply Iff.of_eq
  congr 1
  funext i
  rw [Term.realize_relabel, Sum.elim_comp_inr, ← deepInterp_eq_realize_fin]

/-- **Superset relation atom bridge**: the same relation atom over `S`, realized on the `T`-induced
deep tuple (`S ⊆ T`), holds iff `R` holds in `M` on the deep interpretations over `T`. The relation
analogue of `realize_deEqAtom_superset`, via `deTermFin_realize_superset`. -/
theorem realize_deRelAtom_superset (d : ℕ) {S T : Finset J} (_hST : S ⊆ T) {l : ℕ}
    (R : (skolemColim L).Relations l) (ts : Fin l → (skolemColim L)[[J]].Term Empty)
    (ht : ∀ i, jSupport L J (ts i) ⊆ S) :
    letI : (skolemColim L).Structure M := skolemColimStructure L
    (deRelAtom L J S R ts ht).Realize Empty.elim
        (fun i : Fin S.card => a (d + deepRank J T (S.orderEmbOfFin rfl i))) ↔
      Structure.RelMap R fun i => deepInterp L J a d T (ts i) := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  rw [deRelAtom, BoundedFormulaω.realize_rel]
  apply Iff.of_eq
  congr 1
  funext i
  rw [Term.realize_relabel, Sum.elim_comp_inr, deTermFin_realize_superset]

/-! ### Step 4: eventual deep equality `EMEq` and the carrier -/

/-- **Eventual deep equality**: closed terms `t, u` are identified when, for all sufficiently deep
interpretations of their **combined** skeleton support, they evaluate equally in `M`. (The combined
support means both terms are read against the same ordered finite skeleton.) -/
def EMEq (t u : (skolemColim L)[[J]].Term Empty) : Prop :=
  ∀ᶠ d in Filter.atTop,
    deepInterp L J a d (jSupport L J t ∪ jSupport L J u) t =
      deepInterp L J a d (jSupport L J t ∪ jSupport L J u) u

theorem EMEq.refl (t : (skolemColim L)[[J]].Term Empty) : EMEq L J a t t :=
  Filter.Eventually.of_forall fun _ => rfl

theorem EMEq.symm {t u : (skolemColim L)[[J]].Term Empty} (h : EMEq L J a t u) :
    EMEq L J a u t := by
  unfold EMEq
  rw [Finset.union_comm (jSupport L J u) (jSupport L J t)]
  exact h.mono fun _ hd => hd.symm

/-- **Support-enlargement invariance** (steps 6-7, the atom-slice payoff): if `t, u` are eventually
deep-equal on their combined support `S₀` (i.e. `EMEq t u`) and the de-substituted equality atom of
`S₀` lies in a tail-indiscernible family `Γ`, then they are eventually deep-equal on *any* larger
support `S ⊇ S₀`. Tail indiscernibility identifies the truth of the one arity-`S₀.card` atom on the
consecutive `S₀`-tuple and on the strictly-increasing `S`-tuple; the two atom bridges convert those to
the `S₀`- and `S`-deep equalities. This is the unlock for `EMEq.trans` and the quotient structure's
function/relation congruence. -/
theorem EMEq_eventually_on_superset
    {Γ : Set (Σ n, (skolemColim L).BoundedFormulaω Empty n)}
    (hind : @IsLomega1omegaIndiscernibleOnTail (skolemColim L) M (skolemColimStructure L) a Γ)
    {t u : (skolemColim L)[[J]].Term Empty}
    (hmem : (⟨(jSupport L J t ∪ jSupport L J u).card,
        deEqAtom L J (jSupport L J t ∪ jSupport L J u) t u Finset.subset_union_left
          Finset.subset_union_right⟩ : Σ n, (skolemColim L).BoundedFormulaω Empty n) ∈ Γ)
    (h : EMEq L J a t u) {S : Finset J} (hS : jSupport L J t ∪ jSupport L J u ⊆ S) :
    ∀ᶠ d in Filter.atTop, deepInterp L J a d S t = deepInterp L J a d S u := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  set S₀ := jSupport L J t ∪ jSupport L J u with hS₀def
  obtain ⟨N, hN⟩ := hind hmem
  rw [EMEq, Filter.eventually_atTop] at h
  obtain ⟨N₀, hN₀⟩ := h
  rw [Filter.eventually_atTop]
  refine ⟨max N N₀, fun d hd => ?_⟩
  have hdN : N ≤ d := le_trans (le_max_left _ _) hd
  have hdN₀ : N₀ ≤ d := le_trans (le_max_right _ _) hd
  have hsmono : StrictMono (fun i : Fin S₀.card => d + (i : ℕ)) :=
    fun i i' hii' => Nat.add_lt_add_left hii' d
  have hs'mono : StrictMono (fun i : Fin S₀.card => d + deepRank J S (S₀.orderEmbOfFin rfl i)) := by
    intro i i' hii'
    refine Nat.add_lt_add_left (deepRank_lt_of_lt (J := J) ?_ ((S₀.orderEmbOfFin rfl).strictMono hii')) d
    exact hS (Finset.orderEmbOfFin_mem S₀ rfl i)
  have hiff := hN (fun i => d + (i : ℕ)) (fun i => d + deepRank J S (S₀.orderEmbOfFin rfl i))
    hsmono hs'mono (fun k => le_trans hdN (Nat.le_add_right d k))
    (fun k => le_trans hdN (Nat.le_add_right d _))
  have hb0 := realize_deEqAtom L J a d S₀ t u Finset.subset_union_left Finset.subset_union_right
  have hbS := realize_deEqAtom_superset L J a d hS t u Finset.subset_union_left
    Finset.subset_union_right
  exact hbS.mp (hiff.mp (hb0.mpr (hN₀ d hdN₀)))

/-- **Support-enlargement *iff*** (the symmetric core): on the deep tail the deep equality over the
combined support `S₀` is *equivalent* to the deep equality over any larger support `S ⊇ S₀`. This
gives both directions — descending from a larger support back to `S₀` is what `EMEq.trans` needs (it
works over the union of three supports and must return to the `(t,v)`-support). -/
theorem eventually_deepInterp_superset_iff
    {Γ : Set (Σ n, (skolemColim L).BoundedFormulaω Empty n)}
    (hind : @IsLomega1omegaIndiscernibleOnTail (skolemColim L) M (skolemColimStructure L) a Γ)
    {t u : (skolemColim L)[[J]].Term Empty}
    (hmem : (⟨(jSupport L J t ∪ jSupport L J u).card,
        deEqAtom L J (jSupport L J t ∪ jSupport L J u) t u Finset.subset_union_left
          Finset.subset_union_right⟩ : Σ n, (skolemColim L).BoundedFormulaω Empty n) ∈ Γ)
    {S : Finset J} (hS : jSupport L J t ∪ jSupport L J u ⊆ S) :
    ∀ᶠ d in Filter.atTop,
      (deepInterp L J a d (jSupport L J t ∪ jSupport L J u) t
            = deepInterp L J a d (jSupport L J t ∪ jSupport L J u) u ↔
          deepInterp L J a d S t = deepInterp L J a d S u) := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  obtain ⟨N, hN⟩ := hind hmem
  rw [Filter.eventually_atTop]
  refine ⟨N, fun d hd => ?_⟩
  set S₀ := jSupport L J t ∪ jSupport L J u with hS₀def
  have hsmono : StrictMono (fun i : Fin S₀.card => d + (i : ℕ)) :=
    fun i i' hii' => Nat.add_lt_add_left hii' d
  have hs'mono : StrictMono (fun i : Fin S₀.card => d + deepRank J S (S₀.orderEmbOfFin rfl i)) := by
    intro i i' hii'
    refine Nat.add_lt_add_left (deepRank_lt_of_lt (J := J) ?_ ((S₀.orderEmbOfFin rfl).strictMono hii')) d
    exact hS (Finset.orderEmbOfFin_mem S₀ rfl i)
  have hiff := hN (fun i => d + (i : ℕ)) (fun i => d + deepRank J S (S₀.orderEmbOfFin rfl i))
    hsmono hs'mono (fun k => le_trans hd (Nat.le_add_right d k))
    (fun k => le_trans hd (Nat.le_add_right d _))
  have hb0 := realize_deEqAtom L J a d S₀ t u Finset.subset_union_left Finset.subset_union_right
  have hbS := realize_deEqAtom_superset L J a d hS t u Finset.subset_union_left
    Finset.subset_union_right
  exact Iff.trans hb0.symm (Iff.trans hiff hbS)

/-- **Relation support-independence** (the relation analogue of `eventually_deepInterp_superset_iff`):
on the deep tail, the truth of `R` on the deep interpretations over the combined support `S₀` of the
arguments is equivalent to its truth over any larger support `S ⊇ S₀`. This is what makes the
quotient `RelMap` independent of the chosen common support. -/
theorem eventually_relMap_superset_iff
    {Γ : Set (Σ n, (skolemColim L).BoundedFormulaω Empty n)}
    (hind : @IsLomega1omegaIndiscernibleOnTail (skolemColim L) M (skolemColimStructure L) a Γ)
    {l : ℕ} (R : (skolemColim L).Relations l) {ts : Fin l → (skolemColim L)[[J]].Term Empty}
    (hmem : (⟨(Finset.univ.biUnion fun i => jSupport L J (ts i)).card,
        deRelAtom L J (Finset.univ.biUnion fun i => jSupport L J (ts i)) R ts
          fun i => Finset.subset_biUnion_of_mem (fun i => jSupport L J (ts i)) (Finset.mem_univ i)⟩ :
        Σ n, (skolemColim L).BoundedFormulaω Empty n) ∈ Γ)
    {S : Finset J} (hS : (Finset.univ.biUnion fun i => jSupport L J (ts i)) ⊆ S) :
    letI : (skolemColim L).Structure M := skolemColimStructure L
    ∀ᶠ d in Filter.atTop,
      (Structure.RelMap R
            (fun i => deepInterp L J a d (Finset.univ.biUnion fun i => jSupport L J (ts i)) (ts i)) ↔
        Structure.RelMap R (fun i => deepInterp L J a d S (ts i))) := by
  letI : (skolemColim L).Structure M := skolemColimStructure L
  obtain ⟨N, hN⟩ := hind hmem
  rw [Filter.eventually_atTop]
  refine ⟨N, fun d hd => ?_⟩
  set S₀ := Finset.univ.biUnion fun i => jSupport L J (ts i) with hS₀def
  have hsmono : StrictMono (fun i : Fin S₀.card => d + (i : ℕ)) :=
    fun i i' hii' => Nat.add_lt_add_left hii' d
  have hs'mono : StrictMono (fun i : Fin S₀.card => d + deepRank J S (S₀.orderEmbOfFin rfl i)) := by
    intro i i' hii'
    refine Nat.add_lt_add_left (deepRank_lt_of_lt (J := J) ?_ ((S₀.orderEmbOfFin rfl).strictMono hii')) d
    exact hS (Finset.orderEmbOfFin_mem S₀ rfl i)
  have hiff := hN (fun i => d + (i : ℕ)) (fun i => d + deepRank J S (S₀.orderEmbOfFin rfl i))
    hsmono hs'mono (fun k => le_trans hd (Nat.le_add_right d k))
    (fun k => le_trans hd (Nat.le_add_right d _))
  have hb0 := realize_deRelAtom L J a d S₀ R ts
    fun i => Finset.subset_biUnion_of_mem (fun i => jSupport L J (ts i)) (Finset.mem_univ i)
  have hbS := realize_deRelAtom_superset L J a d hS R ts
    fun i => Finset.subset_biUnion_of_mem (fun i => jSupport L J (ts i)) (Finset.mem_univ i)
  exact Iff.trans hb0.symm (Iff.trans hiff hbS)

/-- The **EM term model carrier**: closed terms of `(skolemColim L)[[J]]` quotiented by eventual
deep equality. (`Quot`, so no equivalence proof is needed to form the carrier; transitivity enters
only when reasoning about the quotient, via support-enlargement invariance.) -/
def EMTermModel : Type := Quot (EMEq L J a)

/-- A closed term as an element of the EM term model. -/
def EMTermModel.mk (t : (skolemColim L)[[J]].Term Empty) : EMTermModel L J a := Quot.mk _ t

end DeepInterp

/-! ### Step 4D-4/5/6: the EM quotient and its structure

To avoid threading the indiscernible sequence, its tail-indiscernible family, and the atomic-diagram
membership through every congruence proof, we bundle them in an `EMContext`. Every quotient operation
then uses `EMEq_eventually_on_superset` (via the support-enlargement *iff*) as its standing congruence
engine. -/

section Quotient

variable {M : Type} [L.Structure M] [Nonempty M]

/-- The **standing data** for the EM quotient over a fixed source model `M`: a sequence `a` of deep
indiscernibles, a tail-indiscernible family `Γ`, and the fact that every de-substituted equality atom
lies in `Γ` (dischargeable since `L^Sk` is countable, so the whole atomic diagram seeds `Γ`). -/
structure EMContext where
  /-- The deep indiscernible sequence. -/
  a : ℕ → M
  /-- The tail-indiscernible formula family. -/
  Γ : Set (Σ n, (skolemColim L).BoundedFormulaω Empty n)
  /-- Tail indiscernibility of `a` on `Γ`. -/
  hind : @IsLomega1omegaIndiscernibleOnTail (skolemColim L) M (skolemColimStructure L) a Γ
  /-- Every de-substituted equality atom is in `Γ`. -/
  atom_mem : ∀ (S : Finset J) (t u : (skolemColim L)[[J]].Term Empty)
    (ht : jSupport L J t ⊆ S) (hu : jSupport L J u ⊆ S),
    (⟨S.card, deEqAtom L J S t u ht hu⟩ : Σ n, (skolemColim L).BoundedFormulaω Empty n) ∈ Γ
  /-- Every de-substituted relation atom is in `Γ`. -/
  rel_mem : ∀ (S : Finset J) {l : ℕ} (R : (skolemColim L).Relations l)
    (ts : Fin l → (skolemColim L)[[J]].Term Empty) (ht : ∀ i, jSupport L J (ts i) ⊆ S),
    (⟨S.card, deRelAtom L J S R ts ht⟩ : Σ n, (skolemColim L).BoundedFormulaω Empty n) ∈ Γ

/-- **Transitivity of `EMEq`** (the congruence engine's first payoff): enlarge to the union of all
three supports, transport both hypotheses up to it via the enlargement *iff*, chain the equalities
in `M`, and descend back to the `(t,v)`-support. -/
theorem EMContext.trans (ctx : EMContext L J (M := M)) {t u v : (skolemColim L)[[J]].Term Empty}
    (h1 : EMEq L J ctx.a t u) (h2 : EMEq L J ctx.a u v) : EMEq L J ctx.a t v := by
  set S := jSupport L J t ∪ jSupport L J u ∪ jSupport L J v with hSdef
  have hsub_tu : jSupport L J t ∪ jSupport L J u ⊆ S := Finset.subset_union_left
  have hsub_uv : jSupport L J u ∪ jSupport L J v ⊆ S :=
    Finset.union_subset
      ((Finset.subset_union_right).trans Finset.subset_union_left) Finset.subset_union_right
  have hsub_tv : jSupport L J t ∪ jSupport L J v ⊆ S :=
    Finset.union_subset
      ((Finset.subset_union_left).trans Finset.subset_union_left) Finset.subset_union_right
  have iff_tu := eventually_deepInterp_superset_iff L J ctx.a ctx.hind
    (ctx.atom_mem _ t u Finset.subset_union_left Finset.subset_union_right) hsub_tu
  have iff_uv := eventually_deepInterp_superset_iff L J ctx.a ctx.hind
    (ctx.atom_mem _ u v Finset.subset_union_left Finset.subset_union_right) hsub_uv
  have iff_tv := eventually_deepInterp_superset_iff L J ctx.a ctx.hind
    (ctx.atom_mem _ t v Finset.subset_union_left Finset.subset_union_right) hsub_tv
  have hS_tu := (h1.and iff_tu).mono (fun _ p => p.2.mp p.1)
  have hS_uv := (h2.and iff_uv).mono (fun _ p => p.2.mp p.1)
  have hS_tv := (hS_tu.and hS_uv).mono (fun _ p => p.1.trans p.2)
  exact (iff_tv.and hS_tv).mono (fun _ p => p.1.mpr p.2)

/-- **Function congruence**: if the arguments are pairwise `EMEq`, so are the function terms. Enlarge
every argument's deep equality up to the whole term's support, combine the finitely many eventual
equalities, and apply `deepInterp_func` (deep interpretation commutes with function application). -/
theorem EMContext.func_congr (ctx : EMContext L J (M := M)) {n : ℕ}
    (f : (skolemColim L)[[J]].Functions n) {ts ts' : Fin n → (skolemColim L)[[J]].Term Empty}
    (h : ∀ i, EMEq L J ctx.a (ts i) (ts' i)) :
    EMEq L J ctx.a (.func f ts) (.func f ts') := by
  unfold EMEq
  set S₀ := jSupport L J (.func f ts) ∪ jSupport L J (.func f ts') with hS₀
  have hi : ∀ i, ∀ᶠ d in Filter.atTop,
      deepInterp L J ctx.a d S₀ (ts i) = deepInterp L J ctx.a d S₀ (ts' i) := by
    intro i
    refine EMEq_eventually_on_superset L J ctx.a ctx.hind
      (ctx.atom_mem _ (ts i) (ts' i) Finset.subset_union_left Finset.subset_union_right) (h i) ?_
    exact Finset.union_subset
      ((jSupport_subterm L J f ts i).trans Finset.subset_union_left)
      ((jSupport_subterm L J f ts' i).trans Finset.subset_union_right)
  refine (Filter.eventually_all.mpr hi).mono (fun d hd => ?_)
  rw [deepInterp_func, deepInterp_func]
  congr 1
  funext i
  exact hd i

/-- `EMEq` is an equivalence relation on closed terms (refl/symm need no context; trans is
`EMContext.trans`). -/
def EMContext.setoid (ctx : EMContext L J (M := M)) : Setoid ((skolemColim L)[[J]].Term Empty) where
  r := EMEq L J ctx.a
  iseqv := ⟨fun t => EMEq.refl L J ctx.a t, fun h => EMEq.symm L J ctx.a h,
    fun h1 h2 => EMContext.trans (L := L) (J := J) ctx h1 h2⟩

/-- The **EM term model carrier** for a context: closed `(skolemColim L)[[J]]`-terms modulo `EMEq`. -/
def EMContext.Carrier (ctx : EMContext L J (M := M)) : Type :=
  Quotient ctx.setoid

/-- A closed term as an element of the carrier. -/
def EMContext.mkClass (ctx : EMContext L J (M := M)) (t : (skolemColim L)[[J]].Term Empty) :
    ctx.Carrier :=
  Quotient.mk ctx.setoid t

/-- A common support covering all argument representatives — the support over which a relation's deep
truth is read. -/
noncomputable def EMContext.commonSupport (ctx : EMContext L J (M := M)) {n : ℕ}
    (xs : Fin n → ctx.Carrier) : Finset J :=
  Finset.univ.biUnion fun i => jSupport L J (Quotient.out (xs i))

/-- The **EM term-model structure** on the carrier: function symbols act by term formation
`f([t̄]) := [func f t̄]` (skeleton constants `c_j` are the arity-0 case, giving the classes `[c_j]`),
and a relation holds iff it holds in `M` on the deep interpretations for all sufficiently deep `d`
(read over a common support of the arguments). Well-definedness is proved separately, via the
enlargement-invariance congruence engine. -/
noncomputable def EMContext.structure (ctx : EMContext L J (M := M)) :
    (skolemColim L)[[J]].Structure ctx.Carrier where
  funMap {_} f xs := Quotient.mk ctx.setoid (Term.func f fun i => Quotient.out (xs i))
  RelMap {n} R xs :=
    ∀ᶠ d in Filter.atTop,
      letI : (skolemColim L).Structure M := skolemColimStructure L
      letI : (constantsOn J).Structure M :=
        constantsOn.structure fun j => ctx.a (d + deepRank J (ctx.commonSupport (xs := xs)) j)
      @Structure.RelMap ((skolemColim L)[[J]]) M _ n R
        fun i => deepInterp L J ctx.a d (ctx.commonSupport (xs := xs)) (Quotient.out (xs i))

/-- **Function interpretation computes on classes** (well-definedness, API form): applying the
interpreted function symbol to a tuple of term-classes gives the class of the function term. Immediate
from `func_congr` and `Quotient.out_eq`. (The arity-0 case is `constMap_mkClass`: skeleton constants
`c_j` interpret as `[c_j]`.) -/
theorem EMContext.funMap_mkClass (ctx : EMContext L J (M := M)) {n : ℕ}
    (f : (skolemColim L)[[J]].Functions n) (ts : Fin n → (skolemColim L)[[J]].Term Empty) :
    @Structure.funMap ((skolemColim L)[[J]]) ctx.Carrier ctx.structure n f
        (fun i => ctx.mkClass (t := ts i)) = ctx.mkClass (t := .func f ts) := by
  apply Quotient.sound
  apply ctx.func_congr
  exact fun i => Quotient.exact (Quotient.out_eq (ctx.mkClass (t := ts i)))

/-- The arity-0 case: a skeleton constant `c_j` (or any `L^Sk`-constant) interprets as the class of
its constant term. -/
theorem EMContext.constMap_mkClass (ctx : EMContext L J (M := M))
    (c : (skolemColim L)[[J]].Functions 0) :
    @Structure.funMap ((skolemColim L)[[J]]) ctx.Carrier ctx.structure 0 c Fin.elim0
      = ctx.mkClass (t := .func c Fin.elim0) := by
  apply Quotient.sound
  apply ctx.func_congr
  exact fun i => i.elim0

end Quotient

end FirstOrder.Language
