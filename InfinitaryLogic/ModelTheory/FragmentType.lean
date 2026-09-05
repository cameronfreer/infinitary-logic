/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Fragment
import InfinitaryLogic.Lomega1omega.Theory

/-!
# Pointed fragment types

The realized type of a finite tuple in a structure, relative to a fragment `F`, is the truth
assignment on the arity slice of `F`:

* `Fragment.slice F n` — the formulas of `F` at arity `n`, as a subtype of the existing syntax.
  No new syntax of types, no enumeration, and the empty slice is admitted.
* `Fragment.realizedType F M a : F.slice n → Bool` — which members of the slice the tuple `a`
  satisfies.  At arity zero this is the truth of each sentence of `F` in `M`
  (`realizedType_zero`).
* Restriction along an inclusion of fragments is precomposition with the slice map
  (`realizedType_le`), and an isomorphism transports pointed types on the nose
  (`realizedType_equiv`).

## Determining covers

`Set.countable_image_of_determining_cover` is the counting kernel: if countably many
descriptions cover a selected set, and any two points satisfying the same description have the
same invariant, the invariant takes countably many values on the set.  The proof is
representative-free: each description contributes a subsingleton image, and coverage puts the
image inside their countable union.  Descriptions may overlap.  Nothing about the cover is
assumed beyond coverage and determination: no measurability, no disjointness, no selector.

Reindexing need not preserve fragment membership: the reindexed formula can be built from the
existing operations (`openBounds`, `mapFreeVars`, `relabel`), but `Fragment` has no reindexing
closure.  `realizedType_reindex` transports types through a supplied slice map satisfying the
semantic reindexing identity; it asserts nothing about membership.

Classical background: fragment types are Marker, *Lectures on Infinitary Model Theory*
(Cambridge, 2016), Definition 2.2.19; the Borel pointed-type map is his Lemma 3.3.2.  The
intrinsic subtype interface and the determining-cover packaging are as implemented here.
-/

namespace Set

/-- **Counting through a determining cover.**  Countably many descriptions `P e` cover `S`, and
any two points of `S` satisfying the same description have the same value of `t`; then `t` takes
countably many values on `S`.  Representative-free: each description contributes a subsingleton
image. -/
theorem countable_image_of_determining_cover {X T E : Type*} [Countable E] (t : X → T)
    (S : Set X) (P : E → X → Prop) (cover : ∀ x ∈ S, ∃ e, P e x)
    (det : ∀ e, ∀ x ∈ S, ∀ y ∈ S, P e x → P e y → t x = t y) : (t '' S).Countable := by
  have hsub : t '' S ⊆ ⋃ e, t '' {x | x ∈ S ∧ P e x} := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, he⟩ := cover x hx
    exact Set.mem_iUnion.mpr ⟨e, x, ⟨hx, he⟩, rfl⟩
  refine Set.Countable.mono hsub (Set.countable_iUnion fun e => ?_)
  apply Set.Subsingleton.countable
  rintro _ ⟨x, ⟨hx, hex⟩, rfl⟩ _ ⟨y, ⟨hy, hey⟩, rfl⟩
  exact det e x hx y hy hex hey

end Set

namespace FirstOrder.Language

variable {L : Language.{u, v}}

namespace Fragment

/-- The arity-`n` slice of a fragment: its members at arity `n`, as a subtype of the syntax. -/
def slice (F : Fragment L) (n : ℕ) : Type (max u v) :=
  {φ : L.BoundedFormulaω Empty n // (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ F}

/-- The slice map of an inclusion of fragments. -/
def sliceMap {F G : Fragment L} (h : F ≤ G) (n : ℕ) : F.slice n → G.slice n :=
  fun φ => ⟨φ.1, le_def.mp h _ φ.2⟩

/-- **The realized `F`-type** of a tuple `a` in `M`: the truth assignment on the arity slice. -/
noncomputable def realizedType (F : Fragment L) (M : Type w) [L.Structure M] {n : ℕ}
    (a : Fin n → M) : F.slice n → Bool :=
  fun φ => @decide (φ.1.Realize (Empty.elim : Empty → M) a) (Classical.propDecidable _)

theorem realizedType_apply_iff (F : Fragment L) (M : Type w) [L.Structure M] {n : ℕ}
    (a : Fin n → M) (φ : F.slice n) :
    F.realizedType M a φ = true ↔ φ.1.Realize (Empty.elim : Empty → M) a := by
  simp [realizedType]

/-- At arity zero the realized type is the truth of each sentence of `F`. -/
theorem realizedType_zero (F : Fragment L) (M : Type w) [L.Structure M] (φ : F.slice 0) :
    F.realizedType M Fin.elim0 φ = true ↔ Sentenceω.Realize φ.1 M :=
  realizedType_apply_iff F M Fin.elim0 φ

/-- **Restriction** along an inclusion of fragments is precomposition with the slice map. -/
theorem realizedType_le {F G : Fragment L} (h : F ≤ G) (M : Type w) [L.Structure M] {n : ℕ}
    (a : Fin n → M) : F.realizedType M a = G.realizedType M a ∘ sliceMap h n :=
  rfl

/-- **Isomorphism invariance**: an isomorphism transports pointed types on the nose. -/
theorem realizedType_equiv (F : Fragment L) {M N : Type w} [L.Structure M] [L.Structure N]
    (e : M ≃[L] N) {n : ℕ} (a : Fin n → M) :
    F.realizedType N (e ∘ a) = F.realizedType M a := by
  funext φ
  apply decide_eq_decide.mpr
  have h := BoundedFormulaω.realize_equiv e φ.1 (Empty.elim : Empty → M) a
  rw [show (⇑e ∘ Empty.elim : Empty → N) = Empty.elim from funext fun x => x.elim] at h
  exact h.symm

/-- **Reindexing need not preserve fragment membership.**  This lemma transports types between
two slices of the same `F` through a supplied slice map `ρ` satisfying the semantic reindexing
identity `hρ` for `σ : Fin m → Fin n`: the type of `a ∘ σ` is the type of `a` read through `ρ`.
Whether the reindexed formulas belong to `F` is exactly what `ρ` supplies. -/
theorem realizedType_reindex (F : Fragment L) (M : Type w) [L.Structure M] {m n : ℕ}
    (σ : Fin m → Fin n) (ρ : F.slice m → F.slice n)
    (hρ : ∀ (φ : F.slice m) (a : Fin n → M),
      (ρ φ).1.Realize (Empty.elim : Empty → M) a ↔ φ.1.Realize (Empty.elim : Empty → M) (a ∘ σ))
    (a : Fin n → M) : F.realizedType M (a ∘ σ) = F.realizedType M a ∘ ρ := by
  funext φ
  exact decide_eq_decide.mpr (hρ φ a).symm

end Fragment

end FirstOrder.Language
