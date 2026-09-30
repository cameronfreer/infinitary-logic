/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.AElementary
import Mathlib.ModelTheory.DirectLimit

/-!
# Fragment elementarity of direct limits

For a directed system of `L`-embeddings whose transition maps are `A`-elementary for a fragment
`A`, the canonical maps into Mathlib's direct limit are `A`-elementary
(`aElementary_directLimit_of`), and fragment sentences and theories hold in the limit iff they hold
in any component (`realize_sentence_directLimit_iff`, `theoryModel_directLimit_iff`).

The proof is an induction on the fragment formula that uses exactly the component closures a
`Fragment` provides (`imp_left_mem`, `imp_right_mem`, `all_mem`, `iInf_mem`, `iSup_mem`); the
transition hypothesis is consumed in the reverse direction of the universal case, where a witness
in the limit is pulled back to a common later component.  No countability of the fragment and no
common ambient structure is assumed: the index type and the carriers live in independent
universes, and `AElementary` is stated across universes for this purpose.  The directed-union
theorem inside one ambient model (`aElementary_iSup`) specializes this to inclusions for
link-to-union elementarity; union-to-ambient elementarity is a separate factorization argument
and is not affected.

Source: Baldwin, Friedman, Koerwien, Laskowski, *Three red herrings* (2014), §3.3, Definition 3.18
and Lemma 3.19, for a fixed fragment.
-/

universe u v v' w

namespace FirstOrder.Language

section DirectLimit

variable {L : Language.{u, v}} {ι : Type v'} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  {G : ι → Type w} [∀ i, L.Structure (G i)] (f : ∀ i j, i ≤ j → G i ↪[L] G j)
  [DirectedSystem G fun i j h ↦ f i j h]

/-- **Direct limits of A-elementary systems**: if every transition map of a directed system is
A-elementary, then so is each canonical map of a component into the direct limit.

This is the fragment form of Baldwin, Friedman, Koerwien, Laskowski, *Three red herrings*
(2014), §3.3, Definition 3.18, Lemma 3.19. The carriers live in `Type w` while the limit lives
in `Type (max v' w)`, which is why `AElementary` takes independent carrier universes. -/
theorem aElementary_directLimit_of (A : Fragment L)
    (hf : ∀ i j (h : i ≤ j), AElementary A (f i j h)) (i : ι) :
    AElementary A (DirectLimit.of L ι G f i) := by
  -- canonical maps commute with the empty-variable valuation
  have h_elim : ∀ (j : ι) {m : ℕ} (xs : Fin m → G j),
      Sum.elim (Empty.elim : Empty → Language.DirectLimit G f) (⇑(DirectLimit.of L ι G f j) ∘ xs)
        = ⇑(DirectLimit.of L ι G f j) ∘ Sum.elim Empty.elim xs := by
    intro j m xs
    funext x
    cases x with
    | inl e => exact e.elim
    | inr k => rfl
  -- the statement proved by induction, simultaneously for every component
  suffices key : ∀ {n : ℕ} (φ : L.BoundedFormulaω Empty n),
      (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A.toSet → ∀ (j : ι) (a : Fin n → G j),
      (φ.Realize Empty.elim (⇑(DirectLimit.of L ι G f j) ∘ a) ↔ φ.Realize Empty.elim a) from
    fun {_} φ hφ a ↦ key φ hφ i a
  intro n φ
  induction φ with
  | falsum => exact fun _ _ _ ↦ Iff.rfl
  | equal t u =>
    intro _ j a
    show t.realize (Sum.elim Empty.elim (⇑(DirectLimit.of L ι G f j) ∘ a))
        = u.realize (Sum.elim Empty.elim (⇑(DirectLimit.of L ι G f j) ∘ a))
      ↔ t.realize (Sum.elim Empty.elim a) = u.realize (Sum.elim Empty.elim a)
    rw [h_elim j a, HomClass.realize_term, HomClass.realize_term]
    exact (DirectLimit.of L ι G f j).injective.eq_iff
  | rel R ts =>
    intro _ j a
    have hts : (fun k ↦ (ts k).realize
        (Sum.elim (Empty.elim : Empty → Language.DirectLimit G f)
          (⇑(DirectLimit.of L ι G f j) ∘ a)))
        = fun k ↦ DirectLimit.of L ι G f j ((ts k).realize (Sum.elim Empty.elim a)) := by
      funext k
      rw [h_elim j a, HomClass.realize_term]
    show Structure.RelMap R (fun k ↦ (ts k).realize
        (Sum.elim Empty.elim (⇑(DirectLimit.of L ι G f j) ∘ a)))
      ↔ Structure.RelMap R (fun k ↦ (ts k).realize (Sum.elim Empty.elim a))
    rw [hts]
    exact (DirectLimit.of L ι G f j).map_rel R _
  | imp φ ψ ihφ ihψ =>
    intro hmem j a
    exact imp_congr (ihφ (A.imp_left_mem hmem) j a) (ihψ (A.imp_right_mem hmem) j a)
  | @all m φ ih =>
    intro hmem j a
    have hbody := A.all_mem hmem
    constructor
    · intro hM b
      have hMb := hM (DirectLimit.of L ι G f j b)
      rw [← Fin.comp_snoc] at hMb
      exact (ih hbody j (Fin.snoc a b)).mp hMb
    · intro hN z
      obtain ⟨j', x, rfl⟩ := DirectLimit.exists_of z
      obtain ⟨k, hjk, hj'k⟩ := directed_of (· ≤ ·) j j'
      -- move the universal from `G j` up to `G k` along the A-elementary transition map
      have hNk : φ.all.Realize Empty.elim (⇑(f j k hjk) ∘ a) :=
        (hf j k hjk φ.all hmem a).mpr hN
      have hsnoc : (Fin.snoc (⇑(DirectLimit.of L ι G f j) ∘ a)
            (DirectLimit.of L ι G f j' x) : Fin (m + 1) → Language.DirectLimit G f)
          = ⇑(DirectLimit.of L ι G f k) ∘ Fin.snoc (⇑(f j k hjk) ∘ a) (f j' k hj'k x) := by
        rw [Fin.comp_snoc, DirectLimit.of_f]
        congr 1
        funext l
        exact DirectLimit.of_f.symm
      rw [hsnoc]
      exact (ih hbody k _).mpr (hNk (f j' k hj'k x))
  | iSup φs ih =>
    intro hmem j a
    exact exists_congr fun k ↦ ih k (A.iSup_mem hmem k) j a
  | iInf φs ih =>
    intro hmem j a
    exact forall_congr' fun k ↦ ih k (A.iInf_mem hmem k) j a

/-- A fragment sentence holds in the direct limit of an A-elementary directed system iff it
holds in any component. -/
theorem realize_sentence_directLimit_iff (A : Fragment L)
    (hf : ∀ i j (h : i ≤ j), AElementary A (f i j h)) (i : ι) {φ : L.Sentenceω}
    (hφ : (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A.toSet) :
    Sentenceω.Realize φ (Language.DirectLimit G f) ↔ Sentenceω.Realize φ (G i) :=
  AElementary.realize_sentence_iff (aElementary_directLimit_of f A hf i) hφ

/-- A fragment theory is modelled by the direct limit of an A-elementary directed system iff it
is modelled by any component. -/
theorem theoryModel_directLimit_iff (A : Fragment L)
    (hf : ∀ i j (h : i ≤ j), AElementary A (f i j h)) (i : ι) {T : Set L.Sentenceω}
    (hT : ∀ φ ∈ T, (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A.toSet) :
    Theoryω.Model T (Language.DirectLimit G f) ↔ Theoryω.Model T (G i) :=
  AElementary.theoryModel_iff (aElementary_directLimit_of f A hf i) hT

end DirectLimit

end FirstOrder.Language
