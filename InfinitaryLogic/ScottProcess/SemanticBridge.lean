/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ScottProcess.Semantic
import InfinitaryLogic.Scott.BFEquivRelabel

/-!
# Semantic entries and back-and-forth equivalence

Two injective tuples `a : Fin n ↪ M` and `b : Fin n ↪ N` of infinite structures over a
relational language have the same semantic entry at level `α` iff they are back-and-forth
equivalent at level `α` (`sf_eq_iff_bfEquiv`).  This is Larson, *Scott processes*, Theorem 1.2,
in back-and-forth form: Theorem 1.2 reads equality of the Scott formulas `φ^M_{a,α}` and
`φ^N_{b,α}` as agreement on the formulas of quantifier depth at most `α`, and `BFEquiv α` is the
semantic form of that agreement.  Tuples with repeated coordinates are compared through the
entries of their synchronized enumerations (`bfEquiv_iff_sf_eq_of_comp_eq`,
`bfEquiv_iff_exists_sf_eq`).

## Main declarations

* `sf_eq_iff_bfEquiv`: `sf L α a = sf L α b ↔ BFEquiv α n a b` for injective tuples of two
  infinite structures in independent universes, at every level `α`; `sf_eq_iff_bfEquiv_self`
  is the one-structure form.
* `bfEquiv_iff_sf_eq_of_comp_eq`: for arbitrary tuples `a = e ∘ g` and `b = e' ∘ g` with
  injective `e`, `e'` and surjective `g` (as produced by
  `exists_embedding_comp_eq_of_eq_iff`), `BFEquiv α n a b ↔ sf L α e = sf L α e'`.
* `bfEquiv_iff_exists_sf_eq`: arbitrary tuples are back-and-forth equivalent at level `α` iff
  they factor through one `g` as `e ∘ g` and `e' ∘ g` with equal entries of `e` and `e'`.

## Interpretation choices

* **Universes.** `M : Type w` and `N : Type w'` are independent, as in `sf_trans_equiv`: the
  entries live in `Ψ (relAtomic L) α n`, which does not depend on the structure, so the bridge
  compares tuples of structures of different universes by an equation.  The rows are indexed
  by `Ordinal.{0}`, as in `ScottProcess/FreeArray.lean`, so the bridge is stated for
  `BFEquiv` at `Ordinal.{0}`.  This is a universe boundary, not a countability restriction:
  every `α : Ordinal.{0}` is allowed, and the transfer to `Ordinal.{w}` for structures in
  `Type w` is `BFEquiv.ofOrdinalLift`/`BFEquiv.toOrdinalLift`, which needs both carriers in
  one `Type w`; the cross-universe bridge therefore has no ordinal-universe transfer.  The
  general `BFEquiv` facts this file uses (`BFEquiv.eq_iff_eq`, `mem_range_iff_of_bfEquiv`,
  `BFEquiv.comp_iff_of_surjective`) live in `Scott/BFEquivRelabel.lean` and hold at every
  ordinal universe.
* **Fresh and repeated points.** In the successor step, a point `m` of `M` that already occurs
  in `a`, say `m = a i`, is answered by `b i`: the relabelling of `BFEquiv α n a b` along
  `Fin.snoc id i` (`BFEquiv.relabel`).  A fresh point `m ∉ range a` is answered through the
  extension sets, which contain the entries of fresh one-point extensions only
  (`mem_E_sf_iff`); conversely the equality atoms of `BFEquiv` force the answer to a fresh
  point to be fresh (`mem_range_iff_of_bfEquiv`).
* **Repeated coordinates.** `BFEquiv` compares arbitrary tuples `Fin n → M`, while entries exist
  for injective tuples only.  An equivalence at any level forces a common equality pattern
  (`BFEquiv.eq_iff_eq`, the equality atoms at level `0`), so
  `exists_embedding_comp_eq_of_eq_iff` factors the two
  tuples through one surjective `g`.  Relabelling along any map preserves back-and-forth
  equivalence (`BFEquiv.relabel`), and along a surjective map it also reflects it
  (`BFEquiv.comp_iff_of_surjective`), with no further hypothesis; along a map that forgets a
  coordinate it does not reflect it.

## References

* Paul B. Larson, *Scott processes*, in *Beyond First Order Model Theory*, vol. I
  (J. Iovino, ed.), CRC Press, 2017, ch. 2.  Numbering follows the book: Definition 1.1 (the
  Scott formula of a tuple), Theorem 1.2 (equal Scott formulas as equal theories of quantifier
  depth `α`), which Larson calls a well-known fact provable by induction on `α`, referring to
  W. Hodges, *Model Theory*, Cambridge University Press, 1993, Theorem 3.5.2.
* In this library, `BFEquiv_implies_agreeQR` gives the forward direction from `BFEquiv` to
  agreement on formulas of bounded quantifier rank at every level, and
  `BFEquiv_iff_agree_formulas_omega` the equivalence for countable structures below `ω₁`.
-/

open Order FirstOrder FirstOrder.Language InfinitaryLogic.ScottProcess.FreeArray

universe u v w w'

namespace InfinitaryLogic.ScottProcess.Semantic

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} [L.Structure M] {N : Type w'} [L.Structure N]

/-! ### The bridge -/

section Infinite

variable [Infinite M] [Infinite N]

/-- Entries at a successor level agree iff the entries one level down and the extension sets
agree. -/
private theorem sf_add_one_eq_iff (α : Ordinal.{0}) {n : ℕ} (a : Fin n ↪ M) (b : Fin n ↪ N) :
    sf L (α + 1) a = sf L (α + 1) b ↔
      sf L α a = sf L α b ∧ E (sf L (α + 1) a) = E (sf L (α + 1) b) := by
  refine ⟨fun h ↦ ⟨?_, congrArg E h⟩, fun h ↦ Ψ.ext_succ (by rw [V_sf, V_sf, h.1]) h.2⟩
  rw [← V_sf (lt_add_one α).le a, h, V_sf]

/-- Entries at a limit level agree iff the entries at all lower levels agree. -/
private theorem sf_limit_eq_iff {lam : Ordinal.{0}} (hlam : IsSuccLimit lam) {n : ℕ}
    (a : Fin n ↪ M) (b : Fin n ↪ N) :
    sf L lam a = sf L lam b ↔ ∀ β < lam, sf L β a = sf L β b := by
  refine ⟨fun h β hβ ↦ ?_, fun h ↦ Ψ.ext_limit hlam fun β hβ ↦ by rw [V_sf, V_sf, h β hβ]⟩
  rw [← V_sf hβ.le a, h, V_sf]

omit [L.IsRelational] [Infinite M] [Infinite N] in
/-- A repeated point is answered by the corresponding entry: `a ⌢ a i` and `b ⌢ b i` are
equivalent wherever `a` and `b` are, by relabelling along `Fin.snoc id i`. -/
private theorem bfEquiv_snoc_apply {α : Ordinal} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) α n a b) (i : Fin n) :
    BFEquiv (L := L) α (n + 1) (Fin.snoc a (a i)) (Fin.snoc b (b i)) := by
  have := BFEquiv.relabel α h (Fin.snoc (α := fun _ ↦ Fin n) id i)
  rwa [Fin.comp_snoc, Fin.comp_snoc, Function.comp_id, Function.comp_id] at this

/-- The answering half of the successor step: if the extension sets of `sf (α + 1) a` and
`sf (α + 1) b` agree, and the bridge holds one level down, every point of `M` has an answer in
`N`. -/
private theorem exists_bfEquiv_snoc (α : Ordinal.{0})
    (ih : ∀ {n : ℕ} (a : Fin n ↪ M) (b : Fin n ↪ N),
      sf L α a = sf L α b ↔ BFEquiv (L := L) α n ⇑a ⇑b)
    {n : ℕ} {a : Fin n ↪ M} {b : Fin n ↪ N} (h : BFEquiv (L := L) α n ⇑a ⇑b)
    (hE : E (sf L (α + 1) a) = E (sf L (α + 1) b)) (m : M) :
    ∃ m' : N, BFEquiv (L := L) α (n + 1) (Fin.snoc ⇑a m) (Fin.snoc ⇑b m') := by
  by_cases hm : m ∈ Set.range a
  · obtain ⟨i, rfl⟩ := hm
    exact ⟨b i, bfEquiv_snoc_apply h i⟩
  · obtain ⟨m', hm', he⟩ := mem_E_sf_iff.1 (hE ▸ mem_E_sf_iff.2 ⟨m, hm, rfl⟩)
    exact ⟨m', (ih (Fin.Embedding.snoc a hm) (Fin.Embedding.snoc b hm')).1 he.symm⟩

/-- The inclusion half of the successor step: if every point of `M` has an answer in `N`, and
the bridge holds one level down, the extension set of `sf (α + 1) a` is contained in that of
`sf (α + 1) b`.  The answer to a fresh point is fresh (`mem_range_iff_of_bfEquiv`). -/
private theorem E_subset_of_forth (α : Ordinal.{0})
    (ih : ∀ {n : ℕ} (a : Fin n ↪ M) (b : Fin n ↪ N),
      sf L α a = sf L α b ↔ BFEquiv (L := L) α n ⇑a ⇑b)
    {n : ℕ} {a : Fin n ↪ M} {b : Fin n ↪ N}
    (hf : ∀ m : M, ∃ m' : N, BFEquiv (L := L) α (n + 1) (Fin.snoc ⇑a m) (Fin.snoc ⇑b m')) :
    E (sf L (α + 1) a) ⊆ E (sf L (α + 1) b) := by
  intro y hy
  obtain ⟨m, hm, rfl⟩ := mem_E_sf_iff.1 hy
  obtain ⟨m', hm'⟩ := hf m
  have hfresh : m' ∉ Set.range b := fun hb ↦ hm ((mem_range_iff_of_bfEquiv hm').2 hb)
  exact mem_E_sf_iff.2 ⟨m', hfresh, ((ih _ _).2 hm').symm⟩

/-- **The bridge** (Larson, Scott processes, Theorem 1.2, in back-and-forth form): injective
tuples `a` of `M` and `b` of `N`, infinite structures in independent universes, have the same
semantic entry at level `α` iff they are back-and-forth equivalent at level `α`. -/
theorem sf_eq_iff_bfEquiv (α : Ordinal.{0}) {n : ℕ} (a : Fin n ↪ M) (b : Fin n ↪ N) :
    sf L α a = sf L α b ↔ BFEquiv (L := L) α n ⇑a ⇑b := by
  induction α using Ordinal.limitRecOn generalizing n with
  | zero => rw [sf_zero_eq_sf_zero_iff, BFEquiv.zero]
  | add_one α ih =>
    have hs := BFEquiv.succ (L := L) α ⇑a ⇑b
    rw [Order.succ_eq_add_one] at hs
    rw [sf_add_one_eq_iff, hs, ih a b]
    have ih' : ∀ {n : ℕ} (b : Fin n ↪ N) (a : Fin n ↪ M),
        sf L α b = sf L α a ↔ BFEquiv (L := L) α n ⇑b ⇑a := fun b a ↦
      eq_comm.trans ((ih a b).trans ⟨BFEquiv.symm, BFEquiv.symm⟩)
    refine and_congr_right fun h ↦ ⟨fun hE ↦ ⟨exists_bfEquiv_snoc α ih h hE, fun m' ↦ ?_⟩,
      fun ⟨hf, hb⟩ ↦ (E_subset_of_forth α ih hf).antisymm (E_subset_of_forth α ih' fun m' ↦ ?_)⟩
    · obtain ⟨m, hm⟩ := exists_bfEquiv_snoc α ih' h.symm hE.symm m'
      exact ⟨m, hm.symm⟩
    · obtain ⟨m, hm⟩ := hb m'
      exact ⟨m, hm.symm⟩
  | limit lam hlam ih =>
    rw [sf_limit_eq_iff hlam, BFEquiv.limit lam hlam]
    exact forall₂_congr fun β hβ ↦ ih β hβ a b

omit [Infinite N] in
/-- **The bridge, one structure**: injective tuples `a` and `b` of an infinite structure have
the same semantic entry at level `α` iff they are back-and-forth equivalent at level `α`. -/
theorem sf_eq_iff_bfEquiv_self (α : Ordinal.{0}) {n : ℕ} (a b : Fin n ↪ M) :
    sf L α a = sf L α b ↔ BFEquiv (L := L) α n ⇑a ⇑b :=
  sf_eq_iff_bfEquiv α a b

/-! ### Repeated coordinates -/

/-- **The bridge for repeated coordinates.** If `a = e ∘ g` and `b = e' ∘ g` for injective
`e : Fin k ↪ M`, `e' : Fin k ↪ N` and one surjective `g : Fin n → Fin k` (the synchronized
enumerations of `exists_embedding_comp_eq_of_eq_iff`), then `a` and `b` are back-and-forth
equivalent at level `α` iff `e` and `e'` have the same semantic entry at level `α`.  The step
from `a, b` to `e, e'` is `BFEquiv.comp_iff_of_surjective`; no hypothesis beyond the
surjectivity of `g` is needed. -/
theorem bfEquiv_iff_sf_eq_of_comp_eq (α : Ordinal.{0}) {n k : ℕ} {a : Fin n → M}
    {b : Fin n → N} {e : Fin k ↪ M} {e' : Fin k ↪ N} {g : Fin n → Fin k} (he : ⇑e ∘ g = a)
    (he' : ⇑e' ∘ g = b) (hg : Function.Surjective g) :
    BFEquiv (L := L) α n a b ↔ sf L α e = sf L α e' := by
  subst he he'
  rw [BFEquiv.comp_iff_of_surjective hg, sf_eq_iff_bfEquiv]

/-- **Arbitrary tuples through entries.** Tuples `a : Fin n → M` and `b : Fin n → N`, possibly
with repeated coordinates, are back-and-forth equivalent at level `α` iff they factor through one
`g` as `e ∘ g` and `e' ∘ g`, with `e` and `e'` injective and of the same semantic entry at
level `α`.  Forward, the common equality pattern of `a` and `b` gives the synchronized
enumerations of `exists_embedding_comp_eq_of_eq_iff`; backward, `BFEquiv.relabel` along `g`. -/
theorem bfEquiv_iff_exists_sf_eq (α : Ordinal.{0}) {n : ℕ} (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (L := L) α n a b ↔ ∃ (k : ℕ) (e : Fin k ↪ M) (e' : Fin k ↪ N) (g : Fin n → Fin k),
      ⇑e ∘ g = a ∧ ⇑e' ∘ g = b ∧ sf L α e = sf L α e' := by
  constructor
  · intro h
    obtain ⟨k, e, e', g, he, he', hg⟩ :=
      exists_embedding_comp_eq_of_eq_iff a b h.eq_iff_eq
    exact ⟨k, e, e', g, he, he', (bfEquiv_iff_sf_eq_of_comp_eq α he he' hg).1 h⟩
  · rintro ⟨k, e, e', g, rfl, rfl, h⟩
    exact BFEquiv.relabel α ((sf_eq_iff_bfEquiv α e e').1 h) g

end Infinite

end InfinitaryLogic.ScottProcess.Semantic
