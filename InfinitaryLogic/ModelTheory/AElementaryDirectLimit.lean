/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.AElementary
import Mathlib.ModelTheory.DirectLimit

/-!
# Fragment elementarity of direct limits

The theorem is proved in **cocone form** (`aElementary_of_cocone`): over a directed index, let
`f i j` be `A`-elementary transition embeddings and let `g i : G i ↪[L] M` be compatible
embeddings (`g j ∘ f i j = g i`) into any structure `M` that they jointly cover.  Then every
`g i` is `A`-elementary.  Only directedness, compatibility and covering are used, so neither a
`DirectedSystem` instance nor a nonempty index is assumed, and `M` lives in its own universe.

For Mathlib's direct limit the canonical maps form such a cocone (`DirectLimit.of_f`,
`DirectLimit.exists_of`), which gives `aElementary_directLimit_of`; fragment sentences and
theories then hold in the limit iff they hold in any component
(`realize_sentence_directLimit_iff`, `theoryModel_directLimit_iff`).

The proof is an induction on the fragment formula that uses exactly the component closures a
`Fragment` provides (`imp_left_mem`, `imp_right_mem`, `all_mem`, `iInf_mem`, `iSup_mem`); the
transition hypothesis is consumed in the reverse direction of the universal case, where a witness
in `M` is pulled back to a common later component.  No countability of the fragment is assumed,
and `AElementary` is stated across carrier universes because the components (`Type w`) and the
direct limit (`Type (max v' w)`) live in different ones.

A directed family of substructures `S i` of one structure is a cocone over its union, with the
inclusions `Substructure.inclusion (le_iSup S i)` as the `g i`, so the cocone form also gives
link-to-union elementarity from pairwise `A`-elementary links.  The ambient-model results in
`ModelTheory/AElementaryChains.lean` are proved independently, by Tarski–Vaught, from the
different hypothesis that every link is `A`-elementary in the ambient model:
`aElementary_iSup` is union-to-ambient elementarity and `aElementary_inclusion_iSup` is
link-to-union elementarity.

The induction proof is Marker, *Lectures on Infinitary Model Theory* (Cambridge, 2016),
Lemma 7.2.11, with a fixed fragment and identity fragment maps; the fixed-fragment chain case is
his Exercise 1.1.14.  The statement is Lemma 3.19(3) of Baldwin, Friedman, Koerwien, Laskowski,
*Three red herrings* (2014), §3.3 (with Definition 3.18), which is stated there for ordinal-indexed
systems over varying countable fragments and growing vocabularies.  The theorem here generalizes
the index (any directed preorder) and the fragment notion (any `Fragment`, with no countability),
and specializes to a fixed vocabulary and a fixed fragment.
-/

universe u v v' w w'

namespace FirstOrder.Language

section Cocone

variable {L : Language.{u, v}} {ι : Type v'} [Preorder ι] [IsDirectedOrder ι]
  {G : ι → Type w} [∀ i, L.Structure (G i)] {f : ∀ i j, i ≤ j → G i ↪[L] G j}
  {M : Type w'} [L.Structure M] {g : ∀ i, G i ↪[L] M} {A : Fragment L}

/-- **A-elementary cocones**: if every transition map of a directed family is A-elementary, then
each map of a compatible family of embeddings that jointly covers `M` is A-elementary.

The proof is Marker, *Lectures on Infinitary Model Theory* (Cambridge, 2016), Lemma 7.2.11
(fixed fragment, identity fragment maps); the statement generalizes Lemma 3.19(3) of Baldwin,
Friedman, Koerwien, Laskowski, *Three red herrings* (2014) to an arbitrary directed index and an
arbitrary fragment, over a fixed vocabulary and a fixed fragment. -/
theorem aElementary_of_cocone (hf : ∀ i j (h : i ≤ j), AElementary A (f i j h))
    (hg : ∀ i j (h : i ≤ j) x, g j (f i j h x) = g i x) (hcover : ∀ z : M, ∃ i x, g i x = z)
    (i : ι) : AElementary A (g i) := by
  -- the statement proved by induction, simultaneously for every component
  suffices key : ∀ {n : ℕ} (φ : L.BoundedFormulaω Empty n),
      (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A.toSet → ∀ (j : ι) (a : Fin n → G j),
      (φ.Realize Empty.elim (⇑(g j) ∘ a) ↔ φ.Realize Empty.elim a) from
    fun {_} φ hφ a ↦ key φ hφ i a
  intro n φ
  induction φ with
  | falsum => exact fun _ _ _ ↦ Iff.rfl
  -- atomic cases: the two parameter valuations `Empty → _` agree by subsingleton elimination,
  -- which `convert` supplies
  | equal t u => exact fun _ j a ↦ by convert (g j).realize_equal_comp t u
  | rel R ts => exact fun _ j a ↦ by convert (g j).realize_rel_comp R ts
  | imp φ ψ ihφ ihψ =>
    intro hmem j a
    exact imp_congr (ihφ (A.imp_left_mem hmem) j a) (ihψ (A.imp_right_mem hmem) j a)
  | @all m φ ih =>
    intro hmem j a
    have hbody := A.all_mem hmem
    constructor
    · intro hM b
      have hMb := hM (g j b)
      rw [← Fin.comp_snoc] at hMb
      exact (ih hbody j (Fin.snoc a b)).mp hMb
    · intro hN z
      obtain ⟨j', x, rfl⟩ := hcover z
      obtain ⟨k, hjk, hj'k⟩ := directed_of (· ≤ ·) j j'
      -- move the universal from `G j` up to `G k` along the A-elementary transition map
      have hNk : φ.all.Realize Empty.elim (⇑(f j k hjk) ∘ a) :=
        (hf j k hjk φ.all hmem a).mpr hN
      have hsnoc : (Fin.snoc (⇑(g j) ∘ a) (g j' x) : Fin (m + 1) → M)
          = ⇑(g k) ∘ Fin.snoc (⇑(f j k hjk) ∘ a) (f j' k hj'k x) := by
        rw [Fin.comp_snoc, hg]
        exact congrArg₂ _ (funext fun l ↦ (hg j k hjk (a l)).symm) rfl
      rw [hsnoc]
      exact (ih hbody k _).mpr (hNk (f j' k hj'k x))
  | iSup φs ih =>
    intro hmem j a
    exact exists_congr fun k ↦ ih k (A.iSup_mem hmem k) j a
  | iInf φs ih =>
    intro hmem j a
    exact forall_congr' fun k ↦ ih k (A.iInf_mem hmem k) j a

end Cocone

section DirectLimit

variable {L : Language.{u, v}} {ι : Type v'} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  {G : ι → Type w} [∀ i, L.Structure (G i)] {f : ∀ i j, i ≤ j → G i ↪[L] G j}
  [DirectedSystem G fun i j h ↦ f i j h] {A : Fragment L}

/-- **Direct limits of A-elementary systems**: if every transition map of a directed system is
A-elementary, then so is each canonical map of a component into the direct limit.

This is `aElementary_of_cocone` for the cocone of canonical maps.  The induction proof is Marker,
*Lectures on Infinitary Model Theory* (Cambridge, 2016), Lemma 7.2.11 (fixed fragment, identity
fragment maps); the statement is the fixed-fragment case of Baldwin, Friedman, Koerwien,
Laskowski, *Three red herrings* (2014), §3.3, Definition 3.18, Lemma 3.19(3), over an arbitrary
directed index. The carriers live in `Type w` while the limit lives in `Type (max v' w)`, which is
why `AElementary` takes independent carrier universes. -/
theorem aElementary_directLimit_of (hf : ∀ i j (h : i ≤ j), AElementary A (f i j h)) (i : ι) :
    AElementary A (DirectLimit.of L ι G f i) :=
  aElementary_of_cocone hf (fun _ _ _ _ ↦ DirectLimit.of_f) DirectLimit.exists_of i

/-- A fragment sentence holds in the direct limit of an A-elementary directed system iff it
holds in any component. -/
theorem realize_sentence_directLimit_iff (hf : ∀ i j (h : i ≤ j), AElementary A (f i j h))
    (i : ι) {φ : L.Sentenceω} (hφ : (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A.toSet) :
    Sentenceω.Realize φ (Language.DirectLimit G f) ↔ Sentenceω.Realize φ (G i) :=
  AElementary.realize_sentence_iff (aElementary_directLimit_of hf i) hφ

/-- A fragment theory is modelled by the direct limit of an A-elementary directed system iff it
is modelled by any component. -/
theorem theoryModel_directLimit_iff (hf : ∀ i j (h : i ≤ j), AElementary A (f i j h))
    (i : ι) {T : Set L.Sentenceω}
    (hT : ∀ φ ∈ T, (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A.toSet) :
    Theoryω.Model T (Language.DirectLimit G f) ↔ Theoryω.Model T (G i) :=
  AElementary.theoryModel_iff (aElementary_directLimit_of hf i) hT

end DirectLimit

end FirstOrder.Language
