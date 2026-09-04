/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.Barwise.HenkinClosure
import InfinitaryLogic.Methods.Interpolation.GraphReconstruction

/-!
# The graph universe of a source fragment

The countable-signature, not-necessarily-relational endpoint of the source-fragment adapter
(issue #19), by relationalization applied *before* the proof system.

## Constructions

* `relationalizeTagged` — the sigma-level relationalization of a tagged formula.
* `relationalizeTheory` — the relationalized theory.
* `Fragment.functionSupport F` — the function symbols occurring in members of `F`; countable for
  countable `F`, which is what `graphAxioms` needs.
* `Fragment.graphFragment F hF` — the Henkin closure of the relationalized members together with
  the graph axioms of the support; a fragment of `graphLanguage L`.
* `Fragment.graphUniverse F hF` — its constants-expanded universe.
* `Fragment.graphTheory F hF T` — the relationalized theory with the graph axioms, mapped into
  the constants expansion.

The countability parameter `hF` is not optional: `graphAxioms` is a countable conjunction over
the support.

## Endpoint

`Fragment.exists_countable_model_of_aconsistent_graphUniverse`: a theory in a countable fragment
whose graph theory is consistent **in the graph universe** has a countable `L`-model.  Both
symbol sigmas of `L` are assumed countable (the graph language's relation sigma is their sum);
`L` need not be relational.  This is not the unrestricted arbitrary-language endpoint.  No
derivation-level relationalization is attempted: consistency is hypothesised over the graph
language, and the theorem is named for that hypothesis.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}

/-! ## Graph-symbol countability -/

/-- A graph relation symbol is a base relation or a function symbol. -/
def graphRelCode :
    (Σ n, (graphLanguage L).Relations n) → (Σ n, L.Relations n) ⊕ (Σ n, L.Functions n)
  | ⟨_, .base R⟩ => Sum.inl ⟨_, R⟩
  | ⟨_, .graph f⟩ => Sum.inr ⟨_, f⟩

theorem graphRelCode_injective : Function.Injective (graphRelCode (L := L)) := by
  rintro ⟨n, R⟩ ⟨m, S⟩ h
  cases R <;> cases S <;> simp only [graphRelCode, Sum.inl.injEq, Sum.inr.injEq,
    Sigma.mk.injEq, reduceCtorEq] at h ⊢
  · obtain ⟨rfl, h⟩ := h; exact ⟨rfl, by subst h; rfl⟩
  · obtain ⟨rfl, h⟩ := h; exact ⟨rfl, by subst h; rfl⟩

instance graphLanguage_countable_relations [Countable (Σ l, L.Relations l)]
    [Countable (Σ n, L.Functions n)] : Countable (Σ n, (graphLanguage L).Relations n) :=
  graphRelCode_injective.countable

/-! ## The translations -/

/-- The sigma-level relationalization. -/
def relationalizeTagged : (Σ n, L.BoundedFormulaω Empty n) →
    (Σ n, (graphLanguage L).BoundedFormulaω Empty n)
  | ⟨n, φ⟩ => ⟨n, relationalizeFormula φ⟩

/-- The relationalized theory. -/
def relationalizeTheory (T : L.Theoryω) : (graphLanguage L).Theoryω :=
  relationalizeFormula '' T

namespace Fragment

/-! ## Function support -/

/-- The function symbols occurring in members of a fragment. -/
def functionSupport (F : Fragment L) : Set (Σ n, L.Functions n) :=
  ⋃ p ∈ F.toSet, p.2.functionsIn

theorem functionsIn_subset_functionSupport {F : Fragment L} {n : ℕ}
    {φ : L.BoundedFormulaω Empty n} (h : (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ F) :
    φ.functionsIn ⊆ F.functionSupport :=
  Set.subset_biUnion_of_mem (u := fun p : Σ n, L.BoundedFormulaω Empty n => p.2.functionsIn) h

theorem functionSupport_countable {F : Fragment L} (hF : F.toSet.Countable) :
    F.functionSupport.Countable :=
  hF.biUnion fun p _ => p.2.functionsIn_countable

/-! ## The graph fragment, universe and theory -/

/-- The seed of the graph fragment: the relationalized members and the graph axioms. -/
noncomputable def graphSeed (F : Fragment L) (hF : F.toSet.Countable) :
    Set (Σ n, (graphLanguage L).BoundedFormulaω Empty n) :=
  haveI : Countable ↥F.functionSupport := (functionSupport_countable hF).to_subtype
  relationalizeTagged '' F.toSet ∪ {⟨0, graphAxioms F.functionSupport⟩}

/-- **The graph fragment**: the Henkin closure of the seed, a fragment of `graphLanguage L`. -/
noncomputable def graphFragment (F : Fragment L) (hF : F.toSet.Countable) :
    Fragment (graphLanguage L) :=
  henkinClosure (F.graphSeed hF)

/-- **The graph universe**: the constants-expanded universe of the graph fragment. -/
noncomputable def graphUniverse (F : Fragment L) (hF : F.toSet.Countable) :
    Set ((graphLanguage L)[[ℕ]].Sentenceω) :=
  (F.graphFragment hF).withNatConstantsSentences

/-- **The graph theory** of `T`: the relationalized theory with the graph axioms of the
support, mapped into the constants expansion. -/
noncomputable def graphTheory (F : Fragment L) (hF : F.toSet.Countable) (T : L.Theoryω) :
    (graphLanguage L)[[ℕ]].Theoryω :=
  haveI : Countable ↥F.functionSupport := (functionSupport_countable hF).to_subtype
  BoundedFormulaω.mapLanguage ((graphLanguage L).lhomWithConstants ℕ) ''
    (relationalizeTheory T ∪ {graphAxioms F.functionSupport})

/-! ## Connecting facts -/

theorem graphSeed_countable {F : Fragment L} (hF : F.toSet.Countable) :
    (F.graphSeed hF).Countable :=
  (hF.image _).union (Set.countable_singleton _)

/-- The graph fragment is countable when both symbol sigmas are. -/
theorem graphFragment_countable [Countable (Σ l, L.Relations l)] [Countable (Σ n, L.Functions n)]
    {F : Fragment L} (hF : F.toSet.Countable) : (F.graphFragment hF).toSet.Countable :=
  henkinClosure_countable (graphSeed_countable hF)

/-- The graph universe satisfies the closure interface. -/
theorem henkinClosed_graphUniverse (F : Fragment L) (hF : F.toSet.Countable) :
    HenkinClosed (F.graphUniverse hF) :=
  henkinClosed_withNatConstantsSentences_henkinClosure _

/-- The relationalized theory and the graph axioms lie in the graph fragment's sentence slice. -/
theorem relationalizeTheory_union_axioms_subset_sentenceSlice {F : Fragment L}
    (hF : F.toSet.Countable) {T : L.Theoryω} (hT : T ⊆ F.sentenceSlice) :
    haveI : Countable ↥F.functionSupport := (functionSupport_countable hF).to_subtype
    relationalizeTheory T ∪ {graphAxioms F.functionSupport} ⊆
      (F.graphFragment hF).sentenceSlice := by
  rintro σ (⟨φ, hφ, rfl⟩ | rfl)
  · exact subset_henkinClosure _ (Or.inl ⟨⟨0, φ⟩, hT hφ, rfl⟩)
  · exact subset_henkinClosure _ (Or.inr rfl)

/-- Every source sentence's function support lies in the support covered by the graph axioms. -/
theorem functionsIn_subset_functionSupport_of_mem_sentenceSlice {F : Fragment L} {T : L.Theoryω}
    (hT : T ⊆ F.sentenceSlice) {φ : L.Sentenceω} (hφ : φ ∈ T) :
    φ.functionsIn ⊆ F.functionSupport :=
  functionsIn_subset_functionSupport (hT hφ)

/-! ## The endpoint -/

/-- **Countable model existence over the graph universe (countable signature, not necessarily
relational).**  A theory inside a countable fragment whose graph theory is `AConsistent` **in the
graph universe** has a countable model, as an `L`-structure: the kernel runs over the relational
graph language, the constants are forgotten, and the source structure is reconstructed from the
graph model through the graph axioms.  The theorem is named for its hypothesis; no consistency is
transported across relationalization. -/
theorem exists_countable_model_of_aconsistent_graphUniverse [Countable (Σ l, L.Relations l)]
    [Countable (Σ n, L.Functions n)] {F : Fragment L} (hF : F.toSet.Countable) {T : L.Theoryω}
    (hT : T ⊆ F.sentenceSlice) (hcons : AConsistent (F.graphUniverse hF) (F.graphTheory hF T)) :
    ∃ (M : Type) (_ : L.Structure M) (_ : Nonempty M) (_ : Countable M), Theoryω.Model T M := by
  have : Countable ↥F.functionSupport := (functionSupport_countable hF).to_subtype
  obtain ⟨N, instN, hne, hcount, hmodel⟩ :=
    exists_countable_model_of_aconsistent_henkinClosure (L := graphLanguage L)
      (graphSeed_countable hF) (relationalizeTheory_union_axioms_subset_sentenceSlice hF hT) hcons
  have hAx : Sentenceω.Realize (graphAxioms F.functionSupport) N := hmodel _ (Or.inr rfl)
  refine ⟨N, reconstructStructure F.functionSupport hAx, hne, hcount, fun φ hφ => ?_⟩
  exact (realize_relationalize_reconstruct hAx φ
    (functionsIn_subset_functionSupport_of_mem_sentenceSlice hT hφ) Empty.elim Fin.elim0).mp
    (hmodel _ (Or.inl ⟨φ, hφ, rfl⟩))

end Fragment

end FirstOrder.Language
