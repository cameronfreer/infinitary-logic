# Infinitary Logic in Lean 4

![CI](https://github.com/cameronfreer/infinitary-logic/actions/workflows/build.yml/badge.svg)
[![Latest release](https://img.shields.io/github/v/release/cameronfreer/infinitary-logic?label=release)](https://github.com/cameronfreer/infinitary-logic/releases/latest)

A Lean 4 formalization of infinitary logic (L∞ω and Lω₁ω), Scott sentences, and classical results in infinitary model theory, building on [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

- **[Project page](https://cameronfreer.github.io/infinitary-logic/)**
- **[Blueprint (web)](https://cameronfreer.github.io/infinitary-logic/blueprint/)** · **[Blueprint (pdf)](https://cameronfreer.github.io/infinitary-logic/blueprint/blueprint.pdf)**
- **[API docs](https://cameronfreer.github.io/infinitary-logic/docs/)** · **[Dependency graph](https://cameronfreer.github.io/infinitary-logic/blueprint/dep_graph_document.html)**
- **[Releases](https://github.com/cameronfreer/infinitary-logic/releases)** · **[How to cite](CITATION.cff)**

## Main Results

### Scott analysis and Karp's theorem

- **Scott sentences** — Every countable structure in a countable relational language has a Scott sentence characterizing it up to isomorphism among countable structures.
- **Scott rank < ω₁** — The Scott rank of any countable structure is a countable ordinal.
- **Karp's theorem** — Back-and-forth equivalence at all ordinals characterizes L∞ω elementary equivalence.

### Model theory of Lω₁ω

- **Model existence** — Every countable consistent set of Lω₁ω sentences in a countable language has a countable model (Henkin-style construction, omitting types, Karp completeness).
- **The Morley–Hanf theorem** — ℶ_ω₁ is a Hanf bound for every Lω₁ω sentence, over an arbitrary language with no side hypotheses (`morley_hanf`): a sentence with a model of size ≥ ℶ_ω₁ has models of arbitrarily large cardinality.
  <details><summary>Proof route</summary>

  No extraction is consumed (an injective sequence is already indiscernible on the Morley seed); the Ehrenfeucht–Mostowski tail-template theory of the seed is realized by a Henkin-style ω-stage completion of the countable *schema* sentence universe (pinning a disjunct for every positive countable disjunction and a refuted conjunct for every negative countable conjunction), whose quotient term model carries a fully indiscernible sequence of Henkin constants; symbol countability is discharged by the sentence's own generated sublanguage. Axioms exactly `[propext, Classical.choice, Quot.sound]`.
  </details>
- **The exact Hanf number** — Hanf(Lω₁ω) = ℶ_ω₁ (`Lomega1omegaHanfNumber_eq_beth_omega1`): the Morley–Hanf bound is sharp.
  <details><summary>Proof route</summary>

  The upper half is `morley_hanf` (bounded Erdős–Rado → Marker/schema completion); the lower half is Marker's Exercise 5.3 beth ladder (countable-index syntax → von Neumann hierarchy witnesses `V_{ω+β}` with Mathlib's cardinality computation → a bounded spectrum with maximum exactly ℶ_{α+1} at every stage α < ω₁ → the successor-cofinal supremum). Axioms exactly `[propext, Classical.choice, Quot.sound]`.
  </details>
- **Small models of every infinite size** — a sentence with arbitrarily large models has, at every infinite κ, a model of size exactly κ realizing only countably many complete Lω₁ω-types (`exists_small_model_of_hasArbLargeModels`; Marker, Theorem 11.2).
  <details><summary>Proof route</summary>

  The witnesses are local Ehrenfeucht–Mostowski quotients over highly order-transitive skeletons (ordered fields via cut dilations; every infinite cardinality via lexicographic Hahn-series subfields); the quotient is order-automorphism equivariant, tuples are classified by countably many compressed term codes, and arbitrary languages reduce along a uniform collapsing hom. Axioms exactly `[propext, Classical.choice, Quot.sound]`.
  </details>
- **Complete sentences and categoricity** — every small model of φ satisfies a complete Lω₁ω-sentence entailing φ (`exists_complete_sentence_of_lomega1omegaSmall`), and a κ-categorical φ with arbitrarily large models has a complete completion with a κ-sized model, itself κ-categorical (`exists_complete_kCategorical_of_hasArbLargeModels`) — over countable relational vocabularies.
  <details><summary>Proof route</summary>

  Route: realized-type isolators → one countable controlling fragment → the countable companion via genuine fragment Löwenheim–Skolem → type-preserving back-and-forth → the canonical Scott sentence characterizes arbitrary models at every ordinal (arbitrary-target stabilization). Axioms exactly `[propext, Classical.choice, Quot.sound]`.
  </details>

### Interpolation

- **Craig interpolation** — an Lω₁ω-entailment r₁ ⊨ r₂ over an *arbitrary* language (no hypotheses on L) has an interpolant θ whose function and relation symbols each lie in the intersection of the two roots' occurrence sets, with r₁ ⊨ θ and θ ⊨ r₂ (`craig_interpolation`), plus the PC-separation form (`craig_pcSeparation`).
  <details><summary>Proof route</summary>

  The relational core (`craig_interpolation_relational`) is an inseparability/finite-condition Henkin construction with no countability hypothesis; the arbitrary-language theorem composes it with a relationalization layer — function symbols become graph relations `G_f`, terms flatten to existential graph formulas, totality/functionality axioms translate the entailment via structure reconstruction, and back-translation `G_f(x⃗,y) ↦ f(x⃗)=y` returns the interpolant with the sharp occurrence bounds. Axioms exactly `[propext, Classical.choice, Quot.sound]`.
  </details>
- **Lyndon interpolation** — the polarity refinement of Craig, over an *arbitrary* language with no hypotheses (`lyndon_interpolation`): the interpolant's **positively** occurring relation symbols lie in the intersection of the two roots' positive occurrences, and its **negatively** occurring ones in the intersection of their negative occurrences (function symbols keep the ordinary shared-occurrence condition). This is the **relation-polarity / logical-equality form** of López-Escobar's Theorem 4.1 — his clause (.4) in full, while equality is treated as a *logical* symbol, belongs to neither polarity class, and is unconstrained in the interpolant, so his clause (.3) is **not** claimed.
  <details><summary>Proof route</summary>

  Polarity is a signed occurrence traversal on the existing syntax (antecedents flip, quantifiers and countable connectives preserve, equality contributes nothing) — **no negation-normal form is constructed anywhere** — whose semantic content is that growing positively-occurring relations and shrinking negatively-occurring ones preserves truth. The proof *refines* the Craig engine: only the separator class changes (base positives in `P`, negatives in `N`), the paired family maintains the flipped class `(F₁∩F₂, P₁∩N₂, N₁∩P₂)`, and the countable-completion kernel is consumed unchanged (enforced by the truth-lemma cone guard). The arbitrary-language step reuses Craig's relationalization verbatim: base-relation polarity is preserved on the nose, and the graph relations `G_f` — which may occur with either polarity — back-translate into *equalities* and so vanish. *Non-claims*: no equality-occurrence condition, and no theory/set-level Lyndon separation (false for Lω₁ω by López-Escobar's Theorem 6.3). Craig is recoverable from it (`craig_of_lyndon_interpolation`). Axioms exactly `[propext, Classical.choice, Quot.sound]`.
  </details>

### Definability and undefinability

- **Boundedness and undefinability of well-ordering** — over an *arbitrary* language with a distinguished binary relation, if an Lω₁ω sentence φ has models with strictly increasing chains of every countable length, then some model of φ carries a **relation-preserving map from ℚ** (`exists_model_relPreserving`; Marker, Theorem 4.26). This is deliberately the *raw positive* conclusion — for all q < r, `RelMap lt ![f q, f r]` — with **no injectivity claimed**; injectivity is a separate corollary under irreflexivity of the interpreted relation (`RelPreserving.injective_of_irreflexive`), and it is automatic in the boundedness corollary, where the relation is well-ordered. The **strict-order corollaries**: if every model interprets the relation well-foundedly, some countable ordinal chains into no model (`wellFounded_boundedness`); if every model interprets it as a well-order, a single countable ordinal strictly bounds every model's order type (`wellOrder_type_boundedness`; Marker, Corollary 4.27); hence no sentence has as models exactly the well-orders (`wellOrdering_undefinable`).
  <details><summary>Proof route</summary>

  The engine is a dedicated consistency property forcing the positive rational diagram (base diagram + finite remainders with α-margin gap witnesses at every α < ω₁), completed and realized by the **same generated-universe Henkin kernel built for Craig interpolation** (fair enumeration + quotient term model, `Methods/Henkin/CountableCompletion/`), with symbol countability removed by the generated sublanguage and function symbols by the **Craig relationalization layer reused verbatim** (the distinguished relation survives both translations definitionally). *Non-claims*: the stronger induced-copy / relational-embedding conclusion (complete <-diagram, negative atoms included) is tracked separately as issue #31 and is not part of these theorems; the Keisler-style elementary-end-extension results around Corollary 4.34 are a different machine, tracked as issue #32. Axioms exactly `[propext, Classical.choice, Quot.sound]`.
  </details>
- **The López–Escobar theorem** — over a countable relational vocabulary, a class of coded countable structures is Borel and isomorphism-invariant **iff** it is the model class of a single Lω₁ω-sentence (`lopezEscobar_iff`; the hard direction is `lopez_escobar`, the easy one `lopezEscobar_easy`), equivalently with invariance under the logic action of S∞ = `Equiv.Perm ℕ` (`lopezEscobar_action_iff`), so the Borel invariant classes are exactly the range of `ModelsOf` (`invariantMeasurableSets_eq_range_modelsOf`, issue #28's collection equality).
  <details><summary>Proof route</summary>

  The hard direction is Marker's route (Theorem 4.25), *not* a Borel-hierarchy induction — which would not preserve invariance: the class and its complement are analytic, hence branch projections of cylinder trees along a query-code closed embedding; each tree is coded as a PC class over two **disjoint tagged copies** of a functional witness vocabulary, relationalized through the **Craig relationalization layer reused verbatim**; the two presentations have no common model (glue two tagged expansions of a shared base model, take a countable fragment-elementary substructure, and one code would lie in both the class and its complement); Craig PC-separation then yields a shared-vocabulary sentence which, by the occurrence calculus, mentions only graph images of base relations and so decodes back to Lω₁ω over the base language. Isomorphism invariance is consumed **exactly once** (the reduct-class converse, inside the disjointness lemma) and downward Löwenheim–Skolem exactly once; both final inclusions use only the invariance-free forward presentation. Axioms exactly `[propext, Classical.choice, Quot.sound]`.
  </details>
- **Non-Borelness of the countable well-order class** — the class WO of codes whose distinguished binary relation well-orders the carrier is **not Borel** in the logic space (`wellOrderClass_not_measurableSet`), the descriptive-set-theoretic payoff of Marker's Corollary 4.27.
  <details><summary>Proof route</summary>

  Were WO Borel, López–Escobar would present it as `ModelsOf φ` — but only over *coded* structures, whose carrier is ℕ, so the sentence is conjoined with the Lω₁ω infiniteness axiom (`infiniteAxiom`) to keep finite models from escaping. Any model of the conjunction whose relation fails to be a well-order fails by two incomparable unequal elements or by an infinite descending chain; seeding a countable fragment-elementary substructure with those witnesses preserves the failure and the added conjunct keeps the substructure infinite, so it transports to a code in WO that is not a well-order. Hence every model of the conjunction is well-ordered, Corollary 4.27 bounds all their order types by a single countable α, and the comparison structure of type α + ω transported to ℕ exceeds that bound. This is the cheap half of Π¹₁-completeness of WO; many-one hardness is not claimed. Axioms exactly `[propext, Classical.choice, Quot.sound]`.
  </details>

### Descriptive set theory

- **Silver's theorem & the Silver–Burgess dichotomy** — A Borel equivalence relation on a Polish space has countably many classes or a perfect set of pairwise-inequivalent points (`gandy_harrington_for_relation`); on a standard Borel space the quotient is ≤ ℵ₀ or exactly 2^ℵ₀ (`silverBurgessDichotomy`).
  <details><summary>Proof route</summary>

  Proved via Miller's classical category route: the Kechris–Solecki–Todorcevic G₀-dichotomy (positivity ideals, Lusin separation, fusion), Miller's G_S independence lemma, Kuratowski–Ulam, and Mycielski's theorem — all formalized here.
  </details>
- **Morley counting** — The number of isomorphism classes of countable models of an Lω₁ω sentence is ≤ ℵ₁ or exactly 2^ℵ₀ (`morley_counting`, parametrized by the dichotomy; unconditional via `silverBurgessDichotomy`).

## Scope and Boundaries

The formalization currently covers L∞ω and Lω₁ω syntax and semantics, Scott analysis (atomic diagrams, back-and-forth equivalence, Scott formulas/sentences, height and rank), Karp's theorem and corollaries, model existence via consistency properties, downward Löwenheim–Skolem for Lω₁ω, Hanf numbers, conditional admissible-fragment interfaces (compactness and the Nadel bound are carried as **structure fields / typeclass hypotheses**, not proved — see #18–#20), descriptive set theory of the space of countable structures (Borel complexity of satisfaction, BF-equivalence, and isomorphism; counting dichotomy), and Silver's theorem with the Silver–Burgess dichotomy, **fully proved** via Miller's classical category route: Mycielski's theorem (`Descriptive/Mycielski.lean`), Kuratowski–Ulam (`Descriptive/KuratowskiUlam.lean`), the `G_S` graphs with Miller's independence lemma (`Descriptive/GSGraph.lean`), the KST separation core and positivity ideals (`Descriptive/G0Dichotomy.lean`), and the G₀-dichotomy fusion (`Descriptive/G0Fusion.lean`). The proof route is

> G₀ homomorphism → meager pullback sections → Kuratowski–Ulam → Mycielski → Silver → Silver–Burgess → Morley counting,

and the endpoints `gandy_harrington_for_relation`, `silverBurgessDichotomy`, and the `morley_counting` instantiation all have axioms exactly `[propext, Classical.choice, Quot.sound]`.

The Morley–Hanf theorem is now **unconditional** (`morley_hanf`, `Conditional/MorleyHanfSchemaDischarge.lean`). The historical conditional forms are retained for the record: the original `morley_hanf_of_transfer` (bundled `MorleyHanfTransfer` hypothesis) and the split bridges through `MorleyHanfExtraction` — a residual since shown to be false in ZFC (the Erdős cardinal κ(ω) is inaccessible, so full-indiscernibility extraction at ℶ_ω₁ is unavailable), which is precisely why the proved route runs through the *tail* extraction and a constructed schema term model instead.

## Repository Guide

- `InfinitaryLogic/Linf/` — L∞ω syntax, semantics, operations, countability predicates, quantifier rank
- `InfinitaryLogic/Lomega1omega/` — Lω₁ω syntax, semantics, operations, embedding into L∞ω, quantifier rank
- `InfinitaryLogic/Scott/` — Atomic diagrams, back-and-forth equivalence, Scott formulas/sentences, rank, height (`Height/Defs`, `Height/CanonicalSentence`, `Height/RankBounds`)
- `InfinitaryLogic/Karp/` — Karp's theorem and corollaries for countable structures
- `InfinitaryLogic/Methods/Henkin/` — Consistency properties, Henkin construction, model existence, completeness, omitting types; `Henkin/CountableCompletion/` is the generated-universe completion kernel (fair enumeration + quotient term model) shared by Craig interpolation and the well-ordering arc
- `InfinitaryLogic/Methods/Interpolation/` — Craig interpolation (inseparability engine, relationalization layer, PC separation) and its **Lyndon layer**: the polarity-refined separator class and side bounds, the paired family and consistency property, the signed root gate, and the relationalization polarity gates
- `InfinitaryLogic/Methods/WellOrdering/` — The issue #12 arc: rational-constant coding, base diagram and gap witnesses, the fifteen closure fields, model extraction, and the boundedness/undefinability endpoints
- `InfinitaryLogic/Methods/LopezEscobar/` — The issue #10 arc: the functional witness language and numeral terms, the functional Θ and its relationalized PC sentence, the standard model and code class, the PC-membership interface with tagged gluing and the disjointness lemma (the sole downward Löwenheim–Skolem consumer), and the shared-symbol decoder with the hard theorem
- `InfinitaryLogic/Methods/EM/` — Indiscernible sequences, EM templates, EM realization
- `InfinitaryLogic/ModelTheory/` — Löwenheim–Skolem, Hanf numbers, counting models
- `InfinitaryLogic/Admissible/` — Admissible-fragment **scaffolding** (`Fragment/Core`, `Fragment/Compact`), conditional compactness interfaces, literature-faithful interface (`Barwise/Data`), an externally sound proof system, and the conditional Nadel interface. The honest foundations are tracked in [#18](https://github.com/cameronfreer/infinitary-logic/issues/18)–[#20](https://github.com/cameronfreer/infinitary-logic/issues/20).
- `InfinitaryLogic/Descriptive/` — Borel complexity of the structure space, satisfaction, isomorphism; counting dichotomy, finite-carrier analysis; and a reusable DST library: Cantor-antichain extraction (`CantorAntichain`), Mycielski (`Mycielski`), Kuratowski–Ulam (`KuratowskiUlam`), the `G_S` graphs (`GSGraph`), and the classical G₀-dichotomy machinery (`G0Dichotomy`, `G0Fusion`); the query-code closed embedding and analytic tree normal form (`QueryCode`, `AnalyticTree`) and the López–Escobar facade (`LopezEscobar`)
- `InfinitaryLogic/Conditional/` — The Silver chain (`SilverBurgess`, `SilverCategoryRoute`, `GandyHarrington` — sorry-free) and the Morley–Hanf chain: `MorleyHanfTransfer` (the historical conditional forms and bridges) and `MorleyHanfSchemaDischarge` (the unconditional `morley_hanf` endpoint)

## Getting Started

```bash
git clone https://github.com/cameronfreer/infinitary-logic.git && cd infinitary-logic
lake build
```

To use in your own project, add the dependency to your `lakefile` and import a bundle:

```lean
import InfinitaryLogic.Core         -- syntax, semantics, Scott, Karp
import InfinitaryLogic.Countable    -- model existence, LS, Hanf, EM chain
import InfinitaryLogic.Admissible   -- admissible-fragment interfaces (conditional)
import InfinitaryLogic.Descriptive  -- descriptive set theory of model classes
import InfinitaryLogic.All          -- all of the above (sorry-free)
import InfinitaryLogic.Conditional  -- Silver chain + Morley-Hanf theorem (both proved)
import InfinitaryLogic.Everything   -- everything including Conditional and legacy off-path modules
```

`import InfinitaryLogic` loads the default surface (`InfinitaryLogic.All`), which includes the headline `morley_hanf`; use `import InfinitaryLogic.Everything` for the rest of `Conditional/` and the legacy off-path `Scott/Code.lean` — work-in-progress frontier modules under `Methods/` live in the separate non-default `InfinitaryLogicWIP` target. **The entire tree is sorry-free** (the historical sorry-bearing Erdős–Rado exploration is preserved on the [`archive/legacy-erdos-rado`](https://github.com/cameronfreer/infinitary-logic/tree/archive/legacy-erdos-rado) branch, not in the tree; the load-bearing bounded Erdős–Rado chain is `Combinatorics/PairErdosRadoGeneral.lean`, `Combinatorics/EndHomogeneousErdosRado.lean`, `Combinatorics/FiniteArityErdosRadoInduction.lean`). `InfinitaryLogic/Basic.lean` is a deprecated redirect to `All`.

### Key Declarations

- `BFEquiv` — Back-and-forth equivalence between tuples, indexed by ordinals
- `scottSentence` — The Scott sentence of a countable structure
- `scottRank` — The Scott rank (ordinal measuring complexity of a structure)
- `karp_theorem_w` — Karp's theorem (potential isomorphism ↔ L∞ω-equivalence)
- `model_existence` — Model existence for Lω₁ω consistency properties
- `gandy_harrington_for_relation` — Silver's theorem for Borel equivalence relations on Polish spaces (proved; classical G₀-dichotomy route)
- `silverBurgessDichotomy` — The Silver–Burgess dichotomy on standard Borel spaces (proved)
- `counting_coded_models_dichotomy` — Counting dichotomy for coded ℕ-models (parametrized by `SilverBurgessDichotomy`, which the repository proves)
- `morley_counting` — Morley's counting theorem: ≤ ℵ₁ or 2^ℵ₀ iso classes of countable models (parametrized by `SilverBurgessDichotomy`; unconditional via `silverBurgessDichotomy`)
- `iso_borel_of_bounded_scottHeight` — Isomorphism is Borel under bounded Scott height
- `morley_hanf` — The Morley–Hanf theorem: ℶ_ω₁ is a Hanf bound for every Lω₁ω sentence (proved, no hypotheses)
- `Lomega1omegaHanfNumber_eq_beth_omega1` — **The exact Hanf number**: Hanf(Lω₁ω) = ℶ_ω₁ (proved; upper half `morley_hanf`, lower half the Exercise 5.3 beth ladder over the von Neumann hierarchy)
- `exists_small_model_of_hasArbLargeModels` — **Small models**: models of every infinite size realizing countably many complete types (proved, arbitrary languages)
- `exists_complete_sentence_of_lomega1omegaSmall` / `exists_complete_kCategorical_of_hasArbLargeModels` — **Complete sentences and categoricity**: small models lie in complete subclasses; κ-categorical sentences have κ-categorical complete completions
- `hanfNumber_le_beth_omega1` / `Lomega1omegaHanfNumber_le_beth_omega1` — Per-sentence and global Hanf-number upper bounds
- `morley_hanf_theory` — The Morley–Hanf theorem for countable Lω₁ω-theories
- `craig_interpolation` — **Craig interpolation**: sharp shared-vocabulary interpolants for Lω₁ω over arbitrary languages (proved, no hypotheses)
- `craig_pcSeparation` / `craig_pcSeparation_relational` — The PC-separation (disjunction) forms
- `lyndon_interpolation` / `lyndon_interpolation_relational` — **Lyndon interpolation**: polarity-refined interpolants (positive/negative occurrences separately bounded) over arbitrary languages; relation-polarity / logical-equality form, equality unconstrained
- `exists_model_relPreserving` — **Rational embedding from long chains** (Marker 4.26): chains of every countable length force a model with a relation-preserving map from ℚ (raw positive form; arbitrary languages)
- `wellOrder_type_boundedness` — **Boundedness of well-ordered models** (Marker 4.27): a uniform countable bound on the order types of well-ordered models
- `wellOrdering_undefinable` — **Undefinability of well-ordering**: no Lω₁ω sentence has as models exactly the well-orders
- `lopez_escobar` / `lopezEscobar_iff` / `lopezEscobar_action_iff` — **López–Escobar**: invariant Borel classes of coded countable structures are exactly the Lω₁ω-definable ones (countable relational vocabularies)
- `wellOrderClass_not_measurableSet` — **Non-Borelness of the countable well-order class**: WO is not Borel in the logic space

## References

- Barwise, J. (1975). *Admissible Sets and Structures*. Springer-Verlag.
- Karp, C. R. (1964). *Languages with Expressions of Infinite Length*. North-Holland.
- Karp, C. R. (1965). Finite-Quantifier Equivalence. In *The Theory of Models*, 407–412.
- Keisler, H. J. (1971). *Model Theory for Infinitary Logic*. North-Holland.
- López-Escobar, E. G. K. (1965). An interpolation theorem for denumerably long formulas. *Fundamenta Mathematicae*, 57, 253–272.
- Keisler, H. J. & Knight, J. F. (2004). Barwise: Infinitary Logic and Admissible Sets. *Bulletin of Symbolic Logic*, 10(1), 4–36.
- Marker, D. (2016). *Lectures on Infinitary Model Theory*. Cambridge University Press.
- Nadel, M. E. (1974). Scott sentences and admissible sets. *Annals of Mathematical Logic*, 7(2–3), 267–294.

## License & Citation

Apache 2.0 licensed. See [LICENSE](LICENSE) for details.

```bibtex
@software{freer2026infinitary,
  author = {Cameron Freer},
  title = {Infinitary Logic in {Lean} 4},
  url = {https://github.com/cameronfreer/infinitary-logic},
  year = {2026}
}
```
