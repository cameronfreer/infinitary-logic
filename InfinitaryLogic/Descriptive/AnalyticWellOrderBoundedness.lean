/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.AnalyticTree
import InfinitaryLogic.Descriptive.WellOrderBridge
import InfinitaryLogic.Methods.LopezEscobar.CodeClass
import InfinitaryLogic.ModelTheory.WellOrdering

/-!
# Analytic subsets of the well-order class are bounded (issue #64)

**Boundedness for analytic families of coded well-orders**: if `A` is an analytic set of codes,
every one of which interprets the distinguished relation as a well-order, then a *single*
countable ordinal bounds all their order types.

The classical statement is the boundedness theorem for `Σ¹₁` subsets of `WO`; here it is obtained
through the project's López–Escobar machinery rather than through a rank analysis, by routing an
analytic `A` into a single `L_{ω₁ω}` sentence and then invoking Marker's Corollary 4.27.

## The route

1. `exists_tree_of_analyticSet` puts `A` in tree normal form: `A` is the branch projection of a
   level-indexed cylinder tree `T` along the query code.
2. `pcSentence L .left T` is a sentence `Θ` over the *expanded* language
   `L' := graphLanguage (KLang L)`, and the PC gates sandwich its reduct class:
   `A ⊆ codeReduct '' ModelsOf Θ ⊆ W` for every isomorphism-invariant `W ⊇ A`.
3. Taking `W := wellOrderClass lt` — invariant by `wellOrderClass_isomorphismInvariant`, and a
   superset of `A` by hypothesis — the upper gate says exactly that every model of `Θ` is a
   well-order *for the transported relation* `GraphRelation.base (Sum.inl lt)`.  No transport
   lemma is needed: `codeReduct_toStructure` is `Iff.rfl`, so the two memberships are the same
   proposition.
4. `isWellOrder_of_realize_of_modelsOf_subset` — the containment form of the defect bridge, which
   exists for this consumer — lifts that from codes to arbitrary models of `Θ ⊓ infiniteAxiom`.
5. `wellOrder_type_boundedness` bounds all of those order types by one countable `β`.
6. The lower gate `subset_pcClass` exhibits each `c ∈ A` as `codeReduct d` for a model `d` of `Θ`,
   and `ℕ` is infinite, so the bound applies to `d` — and lands on `c` definitionally.

**Why the arbitrary-language endpoint.**  Step 5 uses `wellOrder_type_boundedness`, not
`wellOrder_type_boundedness_relational`.  The expanded language `L'` carries a graph relation for
every function symbol of `KLang L`, and asserting a `Countable (Σ l, L'.Relations l)` instance here
would re-derive exactly what `Methods/WellOrdering/GraphTranslation.lean` was written to remove.
The public endpoint has no symbol-countability hypothesis; the relationalization is already inside
it.
-/

namespace FirstOrder.Language

open FirstOrder Structure Set

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- **Boundedness for analytic families of coded well-orders** (issue #64): if every code in an
analytic set `A` interprets `lt` as a well-order, then a single countable ordinal `α` strictly
bounds every one of their order types.

The class `A` itself need not be isomorphism-invariant — only the envelope `wellOrderClass lt` is,
which is what the sandwich `A ⊆ codeReduct '' ModelsOf Θ ⊆ wellOrderClass lt` consumes. -/
@[blueprint "thm:analytic-wellorder-boundedness"
  (title := /-- Boundedness for analytic families of coded well-orders -/)
  (statement := /-- If $A$ is an analytic set of codes, every one of which interprets the
    distinguished relation $<$ as a well-order of $\mathbb{N}$, then a single countable ordinal
    $\alpha$ strictly bounds the order type of every code in $A$. -/)
  (proof := /-- Put $A$ in tree normal form and let $\Theta$ be the resulting $PC$ sentence over
    the graph language.  Its reduct class is sandwiched, $A \subseteq \mathrm{codeReduct}\,''\,
    \mathrm{ModelsOf}\ \Theta \subseteq W$, for every isomorphism-invariant $W \supseteq A$;
    take $W$ to be the well-order class, which is invariant and contains $A$ by hypothesis.  The
    upper gate then says every model of $\Theta$ is a coded well-order for the transported
    relation, the defect bridge in containment form lifts that to every model of $\Theta$
    conjoined with the infiniteness axiom, and Corollary~4.27 bounds all those order types by one
    countable $\alpha$.  The lower gate exhibits each code of $A$ as the reduct of such a model,
    and $\mathbb{N}$ is infinite, so the bound applies to it. -/)
  (uses := ["thm:wellordering-boundedness"])]
theorem analytic_wellOrder_type_boundedness {A : Set (StructureSpace L)} (lt : L.Relations 2)
    (hA : MeasureTheory.AnalyticSet A) (hAW : A ⊆ wellOrderClass lt) :
    ∃ α : Ordinal.{0}, α < (Cardinal.aleph 1).ord ∧
      ∀ c ∈ A, ∀ h : IsWellOrder ℕ fun x y : ℕ =>
          @Structure.RelMap L ℕ c.toStructure 2 lt ![x, y],
        @Ordinal.type ℕ (fun x y : ℕ => @Structure.RelMap L ℕ c.toStructure 2 lt ![x, y]) h < α := by
  -- the analytic set in tree normal form
  obtain ⟨T, hT⟩ := exists_tree_of_analyticSet hA
  -- the upper gate of the sandwich, with `wellOrderClass lt` as the invariant envelope
  have hupper : codeReduct '' ModelsOf (pcSentence L .left T) ⊆ wellOrderClass lt :=
    pcClass_subset_of_invariant_superset .left T hT hAW (wellOrderClass_isomorphismInvariant lt)
  -- restated over the expanded language: `codeReduct_toStructure` is `Iff.rfl`, so this is the
  -- same proposition and needs no transport
  have hmodels : ModelsOf (pcSentence L .left T) ⊆
      wellOrderClass (GraphRelation.base (Sum.inl lt) :
        (graphLanguage (KLang L)).Relations 2) := by
    intro d hd
    have hbase : codeReduct d ∈ wellOrderClass lt := hupper ⟨d, hd, rfl⟩
    exact hbase
  -- the bridge lifts coded well-orderedness to every model, and Marker 4.27 bounds them
  obtain ⟨β, hβ, hbound⟩ := wellOrder_type_boundedness
    ((pcSentence L .left T).and (infiniteAxiom (graphLanguage (KLang L))))
    (GraphRelation.base (Sum.inl lt))
    (fun M inst hreal =>
      isWellOrder_of_realize_of_modelsOf_subset (GraphRelation.base (Sum.inl lt)) hmodels M hreal)
  refine ⟨β, hβ, ?_⟩
  -- the lower gate: every code of `A` is the reduct of a model of the PC sentence
  intro c hc
  obtain ⟨d, hd, rfl⟩ := subset_pcClass (B := A) .left T hT hc
  intro _
  have hreal : @Sentenceω.Realize (graphLanguage (KLang L))
      ((pcSentence L .left T).and (infiniteAxiom (graphLanguage (KLang L)))) ℕ d.toStructure := by
    let : (graphLanguage (KLang L)).Structure ℕ := d.toStructure
    have hinf : Sentenceω.Realize (infiniteAxiom (graphLanguage (KLang L))) ℕ :=
      realize_infiniteAxiom.mpr inferInstance
    exact (BoundedFormulaω.realize_and _ _).mpr ⟨hd, hinf⟩
  exact hbound ℕ d.toStructure hreal

/-! ## Pullback along a continuous coding

Boundedness is usually consumed one step removed: an analytic set `B` in some other space carries a
*continuous* assignment of well-order codes, and what needs bounding is a rank read off those codes.
The image `code '' B` is analytic, sits inside `wellOrderClass lt`, and the bound transports back. -/

/-- **Boundedness along a continuous well-order presentation**: if an analytic `B` maps continuously
to codes that are all well-orders, and `rank` computes the order type of those codes, then one
countable ordinal bounds `rank` on `B`.

`hrank` is stated for *every* well-ordering proof, so the hypothesis never mentions a particular
`IsWellOrder` term — the caller supplies whichever one it has. -/
theorem analytic_rank_bounded_of_continuousOn_wellOrderPresentation {X : Type*}
    [TopologicalSpace X] {B : Set X} (lt : L.Relations 2) (hB : MeasureTheory.AnalyticSet B)
    (code : X → StructureSpace L) (hcode : ContinuousOn code B)
    (hWO : ∀ x ∈ B, code x ∈ wellOrderClass lt) (rank : X → Ordinal.{0})
    (hrank : ∀ x ∈ B, ∀ h : IsWellOrder ℕ fun a b : ℕ =>
        @Structure.RelMap L ℕ (code x).toStructure 2 lt ![a, b],
      rank x = @Ordinal.type ℕ
        (fun a b : ℕ => @Structure.RelMap L ℕ (code x).toStructure 2 lt ![a, b]) h) :
    ∃ β : Ordinal.{0}, β < (Cardinal.aleph 1).ord ∧ ∀ x ∈ B, rank x < β := by
  obtain ⟨β, hβ, hbound⟩ := analytic_wellOrder_type_boundedness lt (hB.image_of_continuousOn hcode)
    (by rintro _ ⟨x, hx, rfl⟩; exact hWO x hx)
  exact ⟨β, hβ, fun x hx => (hrank x hx (hWO x hx)).trans_lt
    (hbound (code x) ⟨x, hx, rfl⟩ (hWO x hx))⟩

end FirstOrder.Language
