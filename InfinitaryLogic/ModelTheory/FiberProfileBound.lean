/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.FiberBFRestriction
import InfinitaryLogic.ModelTheory.FiberPrefixDetection

/-!
# The row-profile bound

For the prefix specialization (rows are allowed words, the fiber at `(r, τ)` is the component
`B (last τ)` when `τ ⪯ r` and the default `B_*` otherwise), the **profile** of a row is the
label-indexed family of isomorphism types of its fibers.

* `DefaultLike Lc Bstar B u`: the component `B u` is isomorphic to the default.
* `SepBounded Lc Bstar B A α` (H_sep): for every `N` some level `β_N < α` separates, from the
  default, every non-default-like component at a position `n ≤ N`.
* (H_up) is `UpwardClosed (DefaultLike Lc Bstar B)`: default-like components are upward closed.

**Theorem** (`exists_profile_bound`): under (H_sep) and (H_up), for every row `r` there is
`β < α` such that every row `s` with `row r ≡_β row s` in the assembled structure has fibers
isomorphic to those of `r` at every label.

The proof takes `β := β_{r.length}`.  Restriction (`bfEquiv_restrict_nil`) gives `C(r, τ) ≡_β
C(s, τ)` for every label.  If the non-default prefix sets of `r` and `s` differed, finite-prefix
detection would produce a non-default label of length at most `r.length + 1`, hence ending at a
position at most `r.length`, prefixing exactly one row; its fiber is a non-default-like component
on one side and the default on the other, and the letter is allowed at that position by whichever
row it prefixes, contradicting (H_sep).  With equal non-default prefix sets the fibers are
isomorphic label by label (`prefixFiber_equiv_of_ndPrefixes_eq`): shared or absent prefixes give
literally equal components, and a prefix of one row only carries a default-like component.

Neither countability nor relationality is needed; `DefaultLike` supplies the isomorphism
witnesses.  Nesting, limit assumptions on `α`, and orbit hypotheses do not enter.
-/

namespace FirstOrder.Language

namespace FiberAssembly

universe u v w

variable {U : Type u} [LinearOrder U] {Lc : Language.{v, w}} {Bstar : Type u} {B : U → Type u}
  [Lc.Structure Bstar] [∀ u, Lc.Structure (B u)] {A : ℕ → Set U}

/-- A component is **default-like** when it is isomorphic to the default component. -/
def DefaultLike (Lc : Language.{v, w}) (Bstar : Type u) (B : U → Type u) [Lc.Structure Bstar]
    [∀ u, Lc.Structure (B u)] (u : U) : Prop :=
  Nonempty (B u ≃[Lc] Bstar)

/-- (H_sep) **Separation at bounded positions**: for every `N` some level `β_N < α` separates
every non-default-like component at a position `n ≤ N` from the default. -/
def SepBounded (Lc : Language.{v, w}) (Bstar : Type u) (B : U → Type u) [Lc.Structure Bstar]
    [∀ u, Lc.Structure (B u)] (A : ℕ → Set U) (α : Ordinal) : Prop :=
  ∀ N : ℕ, ∃ β < α, ∀ n ≤ N, ∀ u ∈ A n, ¬ DefaultLike Lc Bstar B u →
    ¬ BFEquiv (L := Lc) β 0 (Fin.elim0 : Fin 0 → B u) (Fin.elim0 : Fin 0 → Bstar)

/-! ### Transport along component indices -/

/-- Equal component indices give isomorphic components. -/
private def compCongr (Lc : Language.{v, w}) (Bstar : Type u) (B : U → Type u)
    [Lc.Structure Bstar] [∀ u, Lc.Structure (B u)] {o o' : Option U} (h : o = o') :
    Comp Bstar B o ≃[Lc] Comp Bstar B o' := by
  subst h
  exact Language.Equiv.refl Lc _

omit [LinearOrder U] in
private theorem bfEquiv_comp_transport {β : Ordinal} {o o' : Option U} {u : U} (ho : o = some u)
    (ho' : o' = none)
    (h : BFEquiv (L := Lc) β 0 (Fin.elim0 : Fin 0 → Comp Bstar B o)
      (Fin.elim0 : Fin 0 → Comp Bstar B o')) :
    BFEquiv (L := Lc) β 0 (Fin.elim0 : Fin 0 → B u) (Fin.elim0 : Fin 0 → Bstar) := by
  subst ho ho'
  exact h

/-- The last letter of a prefix of an allowed row is allowed at the prefix's last position. -/
theorem last_mem_of_prefix {p : Row A} {τ : Label U} (h : τ.1 <+: p.1) :
    τ.last ∈ A (τ.1.length - 1) := by
  have hlt : τ.1.length - 1 < τ.1.length :=
    Nat.sub_lt (List.length_pos_of_ne_nil τ.2) Nat.one_pos
  have hlast : τ.last = p.1[τ.1.length - 1]'(lt_of_lt_of_le hlt h.length_le) := by
    unfold Label.last
    rw [List.getLast_eq_getElem]
    exact h.getElem hlt
  rw [hlast]
  exact p.2.2 _ _

/-! ### Equal non-default prefix sets give isomorphic fibers -/

/-- Rows with the same non-default prefixes have isomorphic fibers at every label: shared or
absent prefixes give literally equal components, and a prefix of one row only carries a
default-like component. -/
theorem prefixFiber_equiv_of_ndPrefixes_eq {r s : Row A}
    (hnd : ndPrefixes (DefaultLike Lc Bstar B) r.1 = ndPrefixes (DefaultLike Lc Bstar B) s.1)
    (τ : Label U) : Nonempty (prefixFiber Bstar B A r τ ≃[Lc] prefixFiber Bstar B A s τ) := by
  show Nonempty (Comp Bstar B (compIndex r.1 τ) ≃[Lc] Comp Bstar B (compIndex s.1 τ))
  by_cases hr : τ.1 <+: r.1 <;> by_cases hs : τ.1 <+: s.1
  · exact ⟨compCongr Lc Bstar B ((compIndex_of_prefix hr).trans (compIndex_of_prefix hs).symm)⟩
  · -- `τ` prefixes `r` only, so it is not a non-default prefix of `r`: its component is
    -- default-like
    have hD : DefaultLike Lc Bstar B τ.last := by
      by_contra hnD
      have : τ ∈ ndPrefixes (DefaultLike Lc Bstar B) r.1 := ⟨hr, hnD⟩
      rw [hnd] at this
      exact hs this.1
    obtain ⟨e⟩ := hD
    have e' : Comp Bstar B (some τ.last) ≃[Lc] Comp Bstar B none := e
    exact ⟨Language.Equiv.comp (Language.Equiv.comp
      (compCongr Lc Bstar B (compIndex_of_not_prefix hs).symm) e')
      (compCongr Lc Bstar B (compIndex_of_prefix hr))⟩
  · have hD : DefaultLike Lc Bstar B τ.last := by
      by_contra hnD
      have : τ ∈ ndPrefixes (DefaultLike Lc Bstar B) s.1 := ⟨hs, hnD⟩
      rw [← hnd] at this
      exact hr this.1
    obtain ⟨e⟩ := hD
    have e' : Comp Bstar B none ≃[Lc] Comp Bstar B (some τ.last) := e.symm
    exact ⟨Language.Equiv.comp (Language.Equiv.comp
      (compCongr Lc Bstar B (compIndex_of_prefix hs).symm) e')
      (compCongr Lc Bstar B (compIndex_of_not_prefix hr))⟩
  · exact ⟨compCongr Lc Bstar B
      ((compIndex_of_not_prefix hr).trans (compIndex_of_not_prefix hs).symm)⟩

/-! ### The profile bound -/

/-- **Row-profile bound**, pointwise form.  Under (H_sep) and (H_up), for every row `r` there is
`β < α` such that any row `s` with `row r ≡_β row s` has fibers isomorphic to those of `r` at
every label. -/
theorem exists_profile_bound (α : Ordinal) (hsep : SepBounded Lc Bstar B A α)
    (hup : UpwardClosed (DefaultLike Lc Bstar B)) (r : Row A) :
    ∃ β < α, ∀ s : Row A,
      BFEquiv (L := lang U Lc) β 1 ![(Carrier.row r : PrefixCarrier Bstar B A)]
        ![(Carrier.row s : PrefixCarrier Bstar B A)] →
      ∀ τ : Label U, Nonempty (prefixFiber Bstar B A r τ ≃[Lc] prefixFiber Bstar B A s τ) := by
  obtain ⟨β, hβ, hsepr⟩ := hsep r.1.length
  refine ⟨β, hβ, fun s hrs => ?_⟩
  -- fiberwise equivalence at level `β`, from restriction
  have hfib : ∀ τ : Label U,
      BFEquiv (L := Lc) β 0 (Fin.elim0 : Fin 0 → prefixFiber Bstar B A r τ)
        (Fin.elim0 : Fin 0 → prefixFiber Bstar B A s τ) :=
    fun τ => bfEquiv_restrict_nil β hrs τ
  -- the non-default prefix sets agree
  have hnd : ndPrefixes (DefaultLike Lc Bstar B) r.1 =
      ndPrefixes (DefaultLike Lc Bstar B) s.1 := by
    by_contra hne
    obtain ⟨τ, hlen, hD, hx⟩ := exists_short_distinguishing_prefix hup s.2.1 hne
    have hpos : τ.1.length - 1 ≤ r.1.length := by omega
    by_cases hr : τ.1 <+: r.1
    · have hs : ¬ τ.1 <+: s.1 := fun hs => hx ⟨fun _ => hs, fun _ => hr⟩
      exact hsepr _ hpos _ (last_mem_of_prefix hr) hD
        (bfEquiv_comp_transport (compIndex_of_prefix hr) (compIndex_of_not_prefix hs) (hfib τ))
    · have hs : τ.1 <+: s.1 := by
        by_contra hs
        exact hx ⟨fun h => absurd h hr, fun h => absurd h hs⟩
      exact hsepr _ hpos _ (last_mem_of_prefix hs) hD
        (bfEquiv_comp_transport (compIndex_of_prefix hs) (compIndex_of_not_prefix hr)
          (hfib τ).symm)
  exact prefixFiber_equiv_of_ndPrefixes_eq hnd

end FiberAssembly

end FirstOrder.Language
