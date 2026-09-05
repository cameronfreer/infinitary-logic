/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.Morleyization
import InfinitaryLogic.ModelTheory.AElementary

/-!
# Morleyization and fragment elementarity

For a fragment `F`, the Morleyization by its members `F.toSet` names every member of `F` by a
predicate.  A base embedding `f : N ↪[L] M` lifts to an embedding of the canonical expansions
exactly when it is `F`-elementary (`exists_morleyEmbedding_iff_aElementary`): an embedding of
expansions must preserve and reflect each new predicate, which is truth agreement on each
member of `F` at every tuple of `N`, and conversely that agreement is precisely what the new
predicates need.  The lift, when it exists, is unique with the given underlying map
(`morleyEmbedding_unique`).

This connects the definitional expansion to the fragment interface directly, without routing
through back-and-forth ranks.  Nothing here asserts quantifier elimination: named members become
atomic, but an arbitrary expanded-language formula need not back-translate into `F`.
-/

namespace FirstOrder.Language

variable {L : Language.{u, v}} (F : Fragment L) {M : Type w} {N : Type w} [L.Structure M]
  [L.Structure N]

/-- An embedding of canonical expansions with a given underlying map. -/
def IsMorleyLift (f : N ↪[L] M)
    (g : @Embedding (L.morleyize F.toSet) N M (morleyExpansion F.toSet N)
      (morleyExpansion F.toSet M)) : Prop :=
  ⇑g = ⇑f

/-- **A base embedding lifts to the canonical expansions iff it is `F`-elementary.** -/
theorem exists_morleyEmbedding_iff_aElementary (f : N ↪[L] M) :
    (∃ g : @Embedding (L.morleyize F.toSet) N M (morleyExpansion F.toSet N)
        (morleyExpansion F.toSet M), IsMorleyLift F f g) ↔ AElementary F f := by
  constructor
  · rintro ⟨g, hg⟩ n φ hφ a
    have h := @Embedding.map_rel (L.morleyize F.toSet) N M (morleyExpansion F.toSet N)
      (morleyExpansion F.toSet M) g n (Sum.inr ⟨φ, hφ⟩) a
    change (φ.Realize Empty.elim (⇑g ∘ a) ↔ φ.Realize Empty.elim a) at h
    rw [hg] at h
    exact h
  · intro h
    refine ⟨@Embedding.mk (L.morleyize F.toSet) N M (morleyExpansion F.toSet N)
      (morleyExpansion F.toSet M) f.toEmbedding (fun {_} φ x => f.map_fun φ x)
      (fun {n} R x => ?_), rfl⟩
    rcases R with R | φ
    · exact f.map_rel R x
    · exact h φ.1 φ.2 x

/-- The lift is unique with the given underlying map. -/
theorem morleyEmbedding_unique (f : N ↪[L] M)
    {g g' : @Embedding (L.morleyize F.toSet) N M (morleyExpansion F.toSet N)
      (morleyExpansion F.toSet M)} (hg : IsMorleyLift F f g) (hg' : IsMorleyLift F f g') :
    g = g' :=
  @Embedding.ext (L.morleyize F.toSet) N M (morleyExpansion F.toSet N) (morleyExpansion F.toSet M)
    g g' fun x => by
      have := congrFun hg x
      have := congrFun hg' x
      simp_all

end FirstOrder.Language
