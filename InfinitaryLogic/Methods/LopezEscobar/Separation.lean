/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.LopezEscobar.SharedDecoder
import InfinitaryLogic.Methods.LopezEscobar.Disjoint
import InfinitaryLogic.Methods.Interpolation.CraigSeparation
import InfinitaryLogic.Descriptive.AnalyticTree

/-!
# López–Escobar, hard direction (issue #10, Unit 5b)

The endpoint: every invariant Borel class of countable `L`-structures is the model class of a
single `L_ω₁ω`-sentence.

The assembly is Marker's, with every ingredient already proved:

1. `B` and `Bᶜ` are analytic, so Unit 0 (`exists_tree_of_analyticSet`) presents each by a
   cylinder tree — `T₀` for `B`, `T₁` for `Bᶜ`;
2. Unit 4 (`pcSentences_entails_not`) says the two PC sentences have no common model;
3. Craig separation (`craig_pcSeparation_relational`, issue #8) separates them by a sentence
   `θ₀` of their shared vocabulary;
4. Unit 5a (`sharedToBase`, `realize_sharedToBase`) decodes `θ₀` into an `L`-sentence and
   transports its truth to base codes;
5. both inclusions then use only the **invariance-free** forward presentation
   `subset_pcClass` (Unit 3a) — one side for `B`, the other for `Bᶜ`.

So `IsomorphismInvariant` is consumed exactly where Unit 3b/Unit 4 already consumed it,
inside `pcSentences_entails_not`; this unit adds no further use of it.
-/

namespace FirstOrder.Language

open FirstOrder Structure Set

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- **López–Escobar, hard direction**: an isomorphism-invariant Borel class of coded
countable `L`-structures is the model class of a single `L_ω₁ω`-sentence. -/
@[blueprint "thm:lopez-escobar"
  (title := /-- López-Escobar, hard direction -/)
  (statement := /-- Over a countable relational vocabulary, every isomorphism-invariant Borel
    class $B$ of coded countable structures is the model class of a single
    $\Lomegaone$-sentence. -/)
  (proof := /-- Marker's route (Theorem~4.25).  $B$ and its complement are Borel, hence
    analytic, so each is the branch projection of a cylinder tree along the query code.  Each
    tree is coded by a sentence $\Theta$ over the base language expanded by two disjoint
    tagged copies of a functional witness vocabulary (a constant, the successor, the code and
    branch functions, and a tree relation at every level), relationalized through the graph
    translation; the base reducts of $\Theta$'s models are exactly $B$, the converse inclusion
    being where isomorphism invariance is consumed.  The two presentations have no common
    model: gluing two tagged expansions of a common base model and passing to a countable
    fragment-elementary substructure would place one code in both $B$ and its complement.
    Craig separation therefore yields a sentence of the shared vocabulary separating them,
    and that vocabulary consists only of graph images of base relation symbols, so the
    separator decodes to an $\Lomegaone$-sentence over the base language.  Both inclusions
    then follow from the invariance-free forward presentation. -/)
  (uses := ["thm:craig-relational"])]
theorem lopez_escobar {B : Set (StructureSpace L)}
    (hB : MeasurableSet B) (hinv : IsomorphismInvariant B) :
    ∃ φ : L.Sentenceω, B = ModelsOf φ := by
  -- (1) tree presentations of `B` and of its complement
  obtain ⟨T₀, hT₀⟩ := exists_tree_of_analyticSet hB.analyticSet
  obtain ⟨T₁, hT₁⟩ := exists_tree_of_analyticSet hB.compl.analyticSet
  -- (2)+(3) the two PC sentences have no common model, so Craig separates them
  obtain ⟨θ₀, hpos, hneg⟩ := craig_pcSeparation_relational (pcSentence L .left T₀)
    (pcSentence L .right T₁) (pcSentences_entails_not T₀ T₁ hT₀ hT₁ hinv)
  -- (4) decode the separator into `L`
  refine ⟨θ₀.mapLanguage (sharedToBase L T₀ T₁), Set.eq_of_subset_of_subset ?_ ?_⟩
  · -- (5a) forward: `B`'s codes carry a left model, on which `θ₀` holds
    intro c hc
    obtain ⟨d, hd, hdc⟩ := subset_pcClass .left T₀ hT₀ hc
    let : (graphLanguage (KLang L)).Structure ℕ := d.toStructure
    have hθ := hpos ℕ hd
    show @Sentenceω.Realize L (θ₀.mapLanguage (sharedToBase L T₀ T₁)) ℕ c.toStructure
    rw [← hdc]
    exact (realize_sharedToBase T₀ T₁ θ₀ d).mp hθ
  · -- (5b) backward: a code outside `B` carries a right model, on which `θ₀` fails
    intro c hc
    by_contra hcB
    obtain ⟨d, hd, hdc⟩ := subset_pcClass .right T₁ hT₁ hcB
    let : (graphLanguage (KLang L)).Structure ℕ := d.toStructure
    refine hneg ℕ hd ((realize_sharedToBase T₀ T₁ θ₀ d).mpr ?_)
    rw [hdc]
    exact hc

end FirstOrder.Language
