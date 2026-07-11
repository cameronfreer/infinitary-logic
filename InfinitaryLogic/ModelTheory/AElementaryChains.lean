/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.FragmentLowenheimSkolem
import Mathlib.Data.Finset.Order

/-!
# Directed unions of A-elementary substructures, and omitting types (issue #13 units 6–7)

Per the frozen audit (`docs/fragments-audit.md` §7–§8): the PRIMARY chain theorem is a
common-ambient directed-union result — a nonempty directed family of A-elementary
substructures of ONE model `M` has an A-elementary directed union (`aElementary_iSup`), and
each link is A-elementary in the union (`aElementary_inclusion_iSup`, via two-out-of-three).
The linearly-ordered chain corollary (`aElementary_iSup_of_monotone`) covers both the ω- and
ω₁-chain forms that #16 consumes; abstract direct limits are deliberately deferred.

The finite-arity `OmitsType` API (unit 7): omission passes down to A-elementary substructures
(`OmitsType.of_aElementary`) and through directed unions (`OmitsType.iSup`) when the type's
formulas lie in the fragment.
-/

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {A : Fragment L}
  {ι : Type*} [Nonempty ι] {S : ι → L.Substructure M}

/-- **The common-ambient directed union theorem**: a nonempty directed family of A-elementary
substructures has an A-elementary union. -/
theorem aElementary_iSup (hdir : Directed (· ≤ ·) S)
    (hS : ∀ i, AElementary A (S i).subtype) :
    AElementary A (⨆ i, S i).subtype := by
  classical
  refine aElementary_of_tarskiVaught _ ?_
  intro n φ hφ a hex
  -- the tuple factors through a single link
  have hmem : ∀ i, ∃ k, (a i : M) ∈ S k := by
    intro i
    exact (Substructure.mem_iSup_of_directed hdir).mp (a i).2
  choose ks hks using hmem
  obtain ⟨k, hk⟩ := hdir.finset_le (Finset.univ.image ks)
  have haS : ∀ i, (a i : M) ∈ S k := fun i =>
    hk (ks i) (Finset.mem_image_of_mem ks (Finset.mem_univ i)) (hks i)
  set â : Fin n → S k := fun i => ⟨(a i : M), haS i⟩ with hâ
  have hcoe : (⇑(⨆ i, S i).subtype ∘ a) = ⇑(S k).subtype ∘ â := funext fun i => rfl
  -- the M-side universal fails, so by A-elementarity of the link it fails in the link
  have hallmem := hφ
  have hagree := hS k φ.all hφ â
  rw [← hcoe] at hagree
  have hMall : ¬(φ.all).Realize (Empty.elim : Empty → M) (⇑(⨆ i, S i).subtype ∘ a) := by
    intro hall
    obtain ⟨m, hm⟩ := hex
    exact hm (hall m)
  have hkall : ¬(φ.all).Realize (Empty.elim : Empty → (S k)) â := fun h =>
    hMall (hagree.mpr h)
  -- extract the link witness and transport it back to M through the link's agreement
  have hkex : ∃ b : S k, ¬φ.Realize (Empty.elim : Empty → (S k)) (Fin.snoc â b) := by
    by_contra hno
    exact hkall fun b => not_not.mp fun hnb => hno ⟨b, hnb⟩
  obtain ⟨b, hb⟩ := hkex
  have hsnoc : (⇑(S k).subtype ∘ Fin.snoc â b : Fin (n + 1) → M)
      = Fin.snoc (⇑(S k).subtype ∘ â) (b : M) :=
    Fin.comp_snoc _ _ _
  have hbagree := hS k φ (A.all_mem hφ) (Fin.snoc â b)
  rw [hsnoc] at hbagree
  refine ⟨⟨(b : M), Substructure.mem_iSup_of_directed hdir |>.mpr ⟨k, b.2⟩⟩, ?_⟩
  show ¬φ.Realize (Empty.elim : Empty → M) (Fin.snoc (⇑(⨆ i, S i).subtype ∘ a) (b : M))
  rw [hcoe]
  exact fun h => hb (hbagree.mp h)

/-- Each link is A-elementary in the union (two-out-of-three). -/
theorem aElementary_inclusion_iSup (hdir : Directed (· ≤ ·) S)
    (hS : ∀ i, AElementary A (S i).subtype) (i : ι) :
    AElementary A (Substructure.inclusion (le_iSup S i)) := by
  have hcomp : (⨆ j, S j).subtype.comp (Substructure.inclusion (le_iSup S i))
      = (S i).subtype := Substructure.subtype_comp_inclusion _
  have h : AElementary A ((⨆ j, S j).subtype.comp (Substructure.inclusion (le_iSup S i))) := by
    rw [hcomp]
    exact hS i
  intro n φ hφ a
  exact AElementary.of_comp (aElementary_iSup hdir hS) h φ hφ a

/-- **The chain corollary** (the ω- and ω₁-chain forms): a monotone chain over a nonempty
linear order has an A-elementary union. -/
theorem aElementary_iSup_of_monotone {ι : Type*} [Nonempty ι] [LinearOrder ι]
    {S : ι → L.Substructure M} (hmono : Monotone S)
    (hS : ∀ i, AElementary A (S i).subtype) :
    AElementary A (⨆ i, S i).subtype :=
  aElementary_iSup (directed_of_isDirected_le hmono) hS

/-! ## Omitting types (unit 7) -/

/-- **Finite-arity type omission**: no tuple realizes every formula of `p`. -/
def OmitsType (M : Type w) [L.Structure M] {n : ℕ}
    (p : Set (L.BoundedFormulaω Empty n)) : Prop :=
  ∀ a : Fin n → M, ∃ φ ∈ p, ¬φ.Realize Empty.elim a

/-- Omission passes down to A-elementary substructures when the type lies in the fragment. -/
theorem OmitsType.of_aElementary {n : ℕ} {p : Set (L.BoundedFormulaω Empty n)}
    {N : L.Substructure M} (hAe : AElementary A N.subtype)
    (hp : ∀ φ ∈ p, (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A.toSet)
    (h : OmitsType M p) : OmitsType (↥N) p := by
  intro a
  obtain ⟨φ, hφp, hφ⟩ := h (⇑N.subtype ∘ a)
  exact ⟨φ, hφp, fun hr => hφ ((hAe φ (hp φ hφp) a).mpr hr)⟩

/-- Omission passes through directed unions of A-elementary links when the type lies in the
fragment: a union tuple lives in one link, which omits, and the link's A-elementarity in the
union transports the failure. -/
theorem OmitsType.iSup (hdir : Directed (· ≤ ·) S)
    (hS : ∀ i, AElementary A (S i).subtype) {n : ℕ}
    {p : Set (L.BoundedFormulaω Empty n)}
    (hp : ∀ φ ∈ p, (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A.toSet)
    (h : ∀ i, OmitsType (↥(S i)) p) : OmitsType (↥(⨆ i, S i)) p := by
  classical
  intro a
  have hmem : ∀ i, ∃ k, (a i : M) ∈ S k := fun i =>
    (Substructure.mem_iSup_of_directed hdir).mp (a i).2
  choose ks hks using hmem
  obtain ⟨k, hk⟩ := hdir.finset_le (Finset.univ.image ks)
  have haS : ∀ i, (a i : M) ∈ S k := fun i =>
    hk (ks i) (Finset.mem_image_of_mem ks (Finset.mem_univ i)) (hks i)
  set â : Fin n → S k := fun i => ⟨(a i : M), haS i⟩ with hâ
  obtain ⟨φ, hφp, hφ⟩ := h k â
  refine ⟨φ, hφp, fun hr => hφ ?_⟩
  -- transport through the link's A-elementarity in the union
  have hlink := aElementary_inclusion_iSup hdir hS k φ (hp φ hφp) â
  have hcoe : (⇑(Substructure.inclusion (le_iSup S k)) ∘ â) = a := by
    funext i
    exact Subtype.ext rfl
  rw [hcoe] at hlink
  exact hlink.mp hr

end Language

end FirstOrder
