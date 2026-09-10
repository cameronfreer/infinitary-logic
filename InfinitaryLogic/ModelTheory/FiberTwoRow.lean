/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.FiberBFAssembly
import InfinitaryLogic.Scott.OrbitRank

/-!
# The two-row lower bound in the prefix specialization

In the prefix specialization (`PrefixCarrier B_* B A`), take a nonempty allowed row `p` ending
in the letter `u`, and the row `q = p ++ [u]` obtained by repeating that last letter.  Under the
**nesting** hypothesis `A n ⊆ A (n + 1)`, `q` is again an allowed row (`isAllowed_concat_last`).
The fibers of `p` and `q` agree at every label except `q` itself
(`compIndex_concat_last_of_ne`), where `p` carries the default component `B_*` and `q` carries
`B u` (`compIndex_concat_last_self`, `compIndex_of_not_prefix`).

**Two-row lower bound** (`twoRow_bfEquiv`, `twoRow_not_automorphic`): if `B u` and `B_*` are
back-and-forth equivalent at level `β` as structures (the empty tuples), the two row elements
are `BFEquiv β` in the assembled language, through the fixed transposition of `p` and `q` and
the generic assembly theorem; and if `B u ≇ B_*`, no automorphism carries the row `p` to the row
`q`, by restricting a putative one to the differing fiber (`restrictFiber`, which is where
relationality of `Lc` enters).  Neither statement needs countability.

**Orbit-rank corollary** (`twoRow_lt_orbitRank`), stated separately: for a countable assembled
structure, the orbit rank of the row `p` exceeds `β`.  This is the only place the orbit
characterization, hence countability, is used.

A **row-tuple corollary** of the generic assembly theorem is supplied on the way
(`fiberBF_of_no_points`): a tuple with no fiber points needs only the empty-tuple data of every
fiber.

No cofinal-rank assembly, full-profile bound, or companion construction appears here.
-/

namespace FirstOrder.Language

namespace FiberAssembly

universe u v w

/-! ### Repeating the last letter of an allowed row -/

section Rows

variable {U : Type u} [LinearOrder U]

/-- Every letter of a nondecreasing list is at most its last letter. -/
theorem le_getLast_of_pairwise {p : List U} (hp : p.Pairwise (· ≤ ·)) (hne : p ≠ [])
    {a : U} (ha : a ∈ p) : a ≤ p.getLast hne := by
  induction p with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    rw [List.pairwise_cons] at hp
    by_cases hxs : xs = []
    · subst hxs
      simp only [List.mem_singleton] at ha
      subst ha
      simp
    · rw [List.getLast_cons hxs]
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hp.1 _ (List.getLast_mem hxs)
      · exact ih hp.2 hxs ha

/-- **Nesting** of the allowed sets: each level's allowed letters remain allowed at the next. -/
def Nested (A : ℕ → Set U) : Prop := ∀ n, A n ⊆ A (n + 1)

/-- Under nesting, repeating the last letter of a nonempty allowed row gives an allowed row. -/
theorem isAllowed_concat_last {A : ℕ → Set U} (hA : Nested A) {p : List U}
    (hp : IsAllowed A p) (hne : p ≠ []) : IsAllowed A (p ++ [p.getLast hne]) := by
  refine ⟨?_, ?_⟩
  · rw [List.pairwise_append]
    refine ⟨hp.1, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb
    subst hb
    exact le_getLast_of_pairwise hp.1 hne ha
  · intro i hi
    rw [List.length_append, List.length_singleton] at hi
    by_cases hlt : i < p.length
    · rw [List.getElem_append_left hlt]
      exact hp.2 i hlt
    · have hi' : i = p.length := by omega
      subst hi'
      rw [List.getElem_append_right le_rfl]
      simp only [Nat.sub_self, List.getElem_singleton]
      -- the last letter is allowed at position `length - 1`, hence at `length` by nesting
      have hpos : 0 < p.length := List.length_pos_of_ne_nil hne
      have hlast := hp.2 (p.length - 1) (by omega)
      rw [← List.getLast_eq_getElem hne] at hlast
      have := hA (p.length - 1) hlast
      rwa [Nat.sub_add_cancel hpos] at this

end Rows

/-! ### The fibers of `p` and `q = p ++ [u]` -/

section Fibers

variable {U : Type u} [LinearOrder U]

/-- The label `q = p ++ [u]` itself. -/
def concatLabel (p : List U) (u : U) : Label U := ⟨p ++ [u], by simp⟩

omit [LinearOrder U] in
theorem concatLabel_last (p : List U) (u : U) : (concatLabel p u).last = u :=
  List.getLast_concat

/-- Away from the label `q`, the fibers of `p` and `q` are indexed alike. -/
theorem compIndex_concat_last_of_ne (p : List U) (u : U) (τ : Label U)
    (hτ : τ ≠ concatLabel p u) : compIndex (p ++ [u]) τ = compIndex p τ := by
  by_cases h : τ.1 <+: p
  · rw [compIndex_of_prefix h, compIndex_of_prefix (h.trans (List.prefix_append _ _))]
  · rw [compIndex_of_not_prefix h, compIndex_of_not_prefix]
    intro h'
    rcases List.prefix_concat_iff.mp h' with h'' | h''
    · exact hτ (Subtype.ext h'')
    · exact h h''

/-- At the label `q`, the fiber of `q` is the component `B u`. -/
theorem compIndex_concat_last_self (p : List U) (u : U) :
    compIndex (p ++ [u]) (concatLabel p u) = some u := by
  rw [compIndex_of_prefix (τ := concatLabel p u) (p := p ++ [u]) (List.prefix_refl _),
    concatLabel_last]

/-- At the label `q`, the fiber of `p` is the default component. -/
theorem compIndex_concat_label_of_shorter (p : List U) (u : U) :
    compIndex p (concatLabel p u) = none := by
  apply compIndex_of_not_prefix
  intro h
  have := h.length_le
  simp [concatLabel] at this

end Fibers

/-! ### A row-tuple corollary of the generic assembly theorem -/

section NoPoints

variable {U : Type u} {Lc : Language.{v, w}} {R S : Type u} {C : R → Label U → Type u}
  {D : S → Label U → Type u} [∀ r τ, Lc.Structure (C r τ)] [∀ s τ, Lc.Structure (D s τ)]

/-- A tuple with no fiber points needs only the empty-tuple data of every fiber. -/
theorem fiberBF_of_no_points {e : R ≃ S} {n : ℕ} {a : Fin n → Carrier R C}
    {b : Fin n → Carrier S D} (hm : Matched e a b)
    (hno : ∀ (i : Fin n) (r : R) (τ : Label U), ¬ InFiber a r τ i) {α : Ordinal}
    (h0 : ∀ (r : R) (τ : Label U),
      BFEquiv (L := Lc) α 0 (Fin.elim0 : Fin 0 → C r τ) (Fin.elim0 : Fin 0 → D (e r) τ)) :
    FiberBF Lc α e hm := by
  intro r τ k ι hι
  cases k with
  | zero =>
    rw [show (fun j : Fin 0 => elt (hι j)) = Fin.elim0 from funext fun j => j.elim0,
      show (fun j : Fin 0 => hm.eltB (hι j)) = Fin.elim0 from funext fun j => j.elim0]
    exact h0 r τ
  | succ k => exact absurd (hι 0) (hno _ r τ)

end NoPoints

/-! ### The two rows -/

section TwoRow

variable {U : Type u} [LinearOrder U] {Lc : Language.{v, w}} {Bstar : Type u} {B : U → Type u}
  [Lc.Structure Bstar] [∀ u, Lc.Structure (B u)] {A : ℕ → Set U}

instance instDecidableEqRow : DecidableEq (Row A) :=
  inferInstanceAs (DecidableEq {p : List U // IsAllowed A p})

omit [LinearOrder U] in
/-- Empty tuples of definitionally identified fibers are equivalent at every level. -/
private theorem bfEquiv_nil_of_compIndex_eq (α : Ordinal) {o o' : Option U} (h : o = o') :
    BFEquiv (L := Lc) α 0 (Fin.elim0 : Fin 0 → Comp Bstar B o)
      (Fin.elim0 : Fin 0 → Comp Bstar B o') := by
  subst h
  exact BFEquiv.refl α _

omit [LinearOrder U] in
/-- Equivalence of `B_*` and `B u` transported to the fibers at indices `none` and `some u`. -/
private theorem bfEquiv_nil_comp (α : Ordinal) {u : U} {o o' : Option U} (ho : o = none)
    (ho' : o' = some u)
    (h : BFEquiv (L := Lc) α 0 (Fin.elim0 : Fin 0 → Bstar) (Fin.elim0 : Fin 0 → B u)) :
    BFEquiv (L := Lc) α 0 (Fin.elim0 : Fin 0 → Comp Bstar B o)
      (Fin.elim0 : Fin 0 → Comp Bstar B o') := by
  subst ho; subst ho'
  exact h

omit [LinearOrder U] in
/-- An isomorphism of the fibers at indices `none` and `some u` is one of `B_*` and `B u`. -/
private def equivComp {u : U} {o o' : Option U} (ho : o = none) (ho' : o' = some u)
    (f : Comp Bstar B o ≃[Lc] Comp Bstar B o') : Bstar ≃[Lc] B u := by
  subst ho; subst ho'
  exact f

/-- The row `q = p ++ [u]`, allowed under nesting. -/
def concatRow (hA : Nested A) (p : Row A) (hne : p.1 ≠ []) : Row A :=
  ⟨p.1 ++ [p.1.getLast hne], isAllowed_concat_last hA p.2 hne⟩

theorem concatRow_ne (hA : Nested A) (p : Row A) (hne : p.1 ≠ []) : concatRow hA p hne ≠ p := by
  intro h
  have := congrArg (fun r : Row A => r.1.length) h
  simp [concatRow] at this

/-- The fixed transposition of the two rows. -/
def twoRowSwap (hA : Nested A) (p : Row A) (hne : p.1 ≠ []) : Row A ≃ Row A :=
  Equiv.swap p (concatRow hA p hne)

theorem twoRowSwap_apply_left (hA : Nested A) (p : Row A) (hne : p.1 ≠ []) :
    twoRowSwap hA p hne p = concatRow hA p hne :=
  Equiv.swap_apply_left _ _

theorem twoRowSwap_apply_right (hA : Nested A) (p : Row A) (hne : p.1 ≠ []) :
    twoRowSwap hA p hne (concatRow hA p hne) = p :=
  Equiv.swap_apply_right _ _

/-- The row elements `p` and `q` are matched along the transposition. -/
theorem twoRow_matched (hA : Nested A) (p : Row A) (hne : p.1 ≠ []) :
    Matched (twoRowSwap hA p hne)
      (![(Carrier.row p : PrefixCarrier Bstar B A)])
      (![(Carrier.row (concatRow hA p hne) : PrefixCarrier Bstar B A)]) := by
  intro i
  fin_cases i
  refine ⟨fun r => ?_, fun r τ => ?_⟩
  · show Carrier.row p = Carrier.row r ↔ Carrier.row (concatRow hA p hne) =
      Carrier.row (twoRowSwap hA p hne r)
    constructor
    · intro h
      rw [← Carrier.row.inj h, twoRowSwap_apply_left]
    · intro h
      have h' := Carrier.row.inj h
      rw [← twoRowSwap_apply_left hA p hne] at h'
      rw [(twoRowSwap hA p hne).injective h']
  · exact iff_of_false
      (not_inFiber_of_eq_row (a := ![(Carrier.row p : PrefixCarrier Bstar B A)]) (i := 0) rfl r τ)
      (not_inFiber_of_eq_row (a := ![(Carrier.row (concatRow hA p hne) : PrefixCarrier Bstar B A)])
        (i := 0) rfl _ τ)

/-- **Two-row equivalence**: if `B u` and `B_*` are equivalent at level `β` as structures, the
row elements `p` and `q` are `BFEquiv β` in the assembled language. -/
theorem twoRow_bfEquiv (hA : Nested A) (p : Row A) (hne : p.1 ≠ []) (β : Ordinal)
    (hβ : BFEquiv (L := Lc) β 0 (Fin.elim0 : Fin 0 → Bstar)
      (Fin.elim0 : Fin 0 → B (p.1.getLast hne))) :
    BFEquiv (L := lang U Lc) β 1 (![(Carrier.row p : PrefixCarrier Bstar B A)])
      (![(Carrier.row (concatRow hA p hne) : PrefixCarrier Bstar B A)]) := by
  refine bfEquiv_of_fiberBF β (twoRow_matched hA p hne) (fiberBF_of_no_points _ ?_ ?_)
  · intro i r τ
    fin_cases i
    exact not_inFiber_of_eq_row (a := ![(Carrier.row p : PrefixCarrier Bstar B A)]) (i := 0)
      rfl r τ
  · intro r τ
    -- the fiber of `r` against the fiber of its image under the transposition
    by_cases hr : r = p
    · subst hr
      rw [twoRowSwap_apply_left]
      by_cases hτ : τ = concatLabel r.1 (r.1.getLast hne)
      · subst hτ
        exact bfEquiv_nil_comp β (compIndex_concat_label_of_shorter _ _)
          (compIndex_concat_last_self _ _) hβ
      · exact bfEquiv_nil_of_compIndex_eq β (compIndex_concat_last_of_ne _ _ τ hτ).symm
    · by_cases hq : r = concatRow hA p hne
      · subst hq
        rw [twoRowSwap_apply_right]
        by_cases hτ : τ = concatLabel p.1 (p.1.getLast hne)
        · subst hτ
          exact BFEquiv.symm (bfEquiv_nil_comp β (compIndex_concat_label_of_shorter _ _)
            (compIndex_concat_last_self _ _) hβ)
        · exact bfEquiv_nil_of_compIndex_eq β (compIndex_concat_last_of_ne _ _ τ hτ)
      · rw [show twoRowSwap hA p hne r = r from Equiv.swap_apply_of_ne_of_ne hr hq]
        exact BFEquiv.refl β _

/-- **No automorphism carries `p` to `q`** when `B u ≇ B_*`: restricting one to the differing
fiber would give an isomorphism `B_* ≃ B u`.  Relationality of `Lc` enters through
`restrictFiber`. -/
theorem twoRow_not_automorphic [Lc.IsRelational] (hA : Nested A) (p : Row A) (hne : p.1 ≠ [])
    (hniso : IsEmpty (Bstar ≃[Lc] B (p.1.getLast hne))) :
    ¬ ∃ g : PrefixCarrier Bstar B A ≃[lang U Lc] PrefixCarrier Bstar B A,
      g (Carrier.row p) = Carrier.row (concatRow hA p hne) := by
  rintro ⟨g, hg⟩
  have hrow : restrictRows g p = concatRow hA p hne := by
    have := restrictRows_apply g p
    rw [hg] at this
    exact (Carrier.row.inj this).symm
  have f := restrictFiber g p (concatLabel p.1 (p.1.getLast hne))
  rw [hrow] at f
  exact hniso.false (equivComp (compIndex_concat_label_of_shorter _ _)
    (compIndex_concat_last_self _ _) f)

/-- **Orbit-rank corollary**, the only statement using countability: in a countable assembled
structure, the orbit rank of the row `p` exceeds `β`. -/
theorem twoRow_lt_orbitRank [Lc.IsRelational] [Countable (PrefixCarrier Bstar B A)]
    (hA : Nested A) (p : Row A) (hne : p.1 ≠ []) (β : Ordinal.{u})
    (hβ : BFEquiv (L := Lc) β 0 (Fin.elim0 : Fin 0 → Bstar)
      (Fin.elim0 : Fin 0 → B (p.1.getLast hne)))
    (hniso : IsEmpty (Bstar ≃[Lc] B (p.1.getLast hne))) :
    β < orbitRank (L := lang U Lc) (![(Carrier.row p : PrefixCarrier Bstar B A)]) := by
  by_contra hle
  push Not at hle
  have hbf := BFEquiv.monotone hle (twoRow_bfEquiv hA p hne β hβ)
  obtain ⟨g, hg⟩ := bfEquiv_orbitRank_iff_exists_automorphism.mp hbf
  exact twoRow_not_automorphic hA p hne hniso ⟨g, congrFun hg 0⟩

end TwoRow

end FiberAssembly

end FirstOrder.Language
