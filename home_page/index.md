---
---

A Lean 4 formalization of **infinitary logic** (L<sub>&infin;&omega;</sub> and L<sub>&omega;<sub>1</sub>&omega;</sub>), **Scott sentences**, and classical results in infinitary model theory, building on [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

**The entire tree is sorry-free**, and every headline result depends on exactly the standard axioms `[propext, Classical.choice, Quot.sound]`.

## Main Results

- **Scott sentences** &mdash; Every countable structure in a countable relational language has a Scott sentence characterizing it up to isomorphism among countable structures.
- **Scott rank < &omega;<sub>1</sub>** &mdash; The Scott rank of any countable structure is a countable ordinal.
- **Karp's theorem** &mdash; Back-and-forth equivalence at all ordinals characterizes L<sub>&infin;&omega;</sub> elementary equivalence.
- **Model existence** &mdash; Every countable consistent set of L<sub>&omega;<sub>1</sub>&omega;</sub> sentences in a countable language has a countable model (Henkin-style construction, omitting types, Karp completeness).
- **Silver's theorem and the Silver&ndash;Burgess dichotomy** &mdash; A Borel equivalence relation on a Polish space has countably many classes or a perfect set of pairwise-inequivalent points; on a standard Borel space the quotient is &le; &alefsym;<sub>0</sub> or exactly 2<sup>&alefsym;<sub>0</sub></sup>. Proved via Miller's classical category route (the G<sub>0</sub>-dichotomy, Kuratowski&ndash;Ulam, Mycielski) &mdash; all formalized here.
- **Morley counting** &mdash; An L<sub>&omega;<sub>1</sub>&omega;</sub> sentence has &le; &alefsym;<sub>1</sub> or exactly 2<sup>&alefsym;<sub>0</sub></sup> isomorphism classes of countable models.
- **The Morley&ndash;Hanf theorem** &mdash; &beth;<sub>&omega;<sub>1</sub></sub> is a Hanf bound for every L<sub>&omega;<sub>1</sub>&omega;</sub> sentence, over an arbitrary language with **no side hypotheses** (`morley_hanf`).
- **The exact Hanf number** &mdash; Hanf(L<sub>&omega;<sub>1</sub>&omega;</sub>) = &beth;<sub>&omega;<sub>1</sub></sub>: the Morley&ndash;Hanf bound is sharp.
- **Small models of every infinite size**, and **complete sentences / categoricity** &mdash; Marker's Theorem 11.2 and its payoff: small models lie in complete subclasses, and &kappa;-categorical sentences have &kappa;-categorical complete completions.
- **Craig interpolation** &mdash; sharp shared-vocabulary interpolants for L<sub>&omega;<sub>1</sub>&omega;</sub> over **arbitrary** languages, plus the PC-separation form.
- **Boundedness and undefinability of well-ordering** &mdash; Marker 4.26/4.27: chains of every countable length force a model with a relation-preserving map from &#8474;; hence a uniform countable bound on the order types of well-ordered models, and no sentence has as models exactly the well-orders.
- **The L&oacute;pez&ndash;Escobar theorem** &mdash; over a countable relational vocabulary, a class of coded countable structures is Borel and isomorphism-invariant **iff** it is the model class of a single L<sub>&omega;<sub>1</sub>&omega;</sub>-sentence (`lopezEscobar_iff`, also in the S<sub>&infin;</sub>-action form), so the invariant Borel classes are exactly the range of `ModelsOf`.
- **Non-Borelness of the countable well-order class** &mdash; the class of codes whose distinguished relation well-orders the carrier is **not Borel** in the logic space. (This is the cheap half of &Pi;<sup>1</sup><sub>1</sub>-completeness; hardness is not claimed.)

## Scope

The formalization currently covers:

- **L<sub>&infin;&omega;</sub> infrastructure** &mdash; syntax (`BoundedFormulaInf` with arbitrary index types for conjunctions/disjunctions), semantics, quantifier rank, and conversions between L<sub>&infin;&omega;</sub> and L<sub>&omega;<sub>1</sub>&omega;</sub>.
- **Scott analysis** &mdash; atomic diagrams, back-and-forth equivalence indexed by ordinals, Scott formulas/sentences, Scott height and rank, and the countable refinement hypothesis (proved).
- **Karp's theorem** &mdash; potential isomorphisms, the main equivalence (`karp_theorem_w`), and corollaries for countable structures.
- **Model existence** &mdash; consistency properties, Henkin construction, truth lemma, model existence, Karp completeness, omitting types, and the generated-universe countable-completion kernel shared by the interpolation and well-ordering arcs.
- **Further model theory** &mdash; downward L&ouml;wenheim&ndash;Skolem (sentence-level and fragment-elementary), Hanf numbers and the exact Hanf number, small models, complete sentences and categoricity, Craig interpolation, and the undefinability of well-ordering.
- **Descriptive set theory** &mdash; the standard Borel structure space, Borel complexity of satisfaction and back-and-forth equivalence, the counting dichotomy, the Silver&ndash;Burgess chain, the S<sub>&infin;</sub> logic action with the invariant &sigma;-algebras, and the L&oacute;pez&ndash;Escobar theorem with its non-Borelness corollary.
- **Admissible fragments** &mdash; Barwise compactness, Barwise completeness II, and the Nadel bound.

Work in progress lives in the separate non-default `InfinitaryLogicWIP` target (currently the Lyndon-interpolation groundwork). It is sorry-free as well, but its statements are not part of the public surface.

## Import Bundles

| Bundle | Contents |
|--------|----------|
| `InfinitaryLogic.Core` | Syntax, semantics, Scott analysis, Karp&rsquo;s theorem, polarity |
| `InfinitaryLogic.Countable` | Model existence, L&ouml;wenheim&ndash;Skolem, Hanf, counting, EM chain |
| `InfinitaryLogic.Admissible` | Admissible fragments, Barwise compactness, proof system |
| `InfinitaryLogic.Descriptive` | Descriptive set theory of model classes, L&oacute;pez&ndash;Escobar |
| `InfinitaryLogic.Conditional` | The Silver chain and the Morley&ndash;Hanf chain (both proved; the directory name is historical) |
| `InfinitaryLogic.All` | The sorry-free default surface (also available via `import InfinitaryLogic`) |
| `InfinitaryLogic.Everything` | All of the above plus the legacy off-path modules |

`InfinitaryLogic/Basic.lean` is a deprecated redirect to `All`.

## Components

| Directory | Contents |
|-----------|----------|
| `InfinitaryLogic/Linf/` | L<sub>&infin;&omega;</sub> syntax, semantics, operations, countability predicates, quantifier rank |
| `InfinitaryLogic/Lomega1omega/` | L<sub>&omega;<sub>1</sub>&omega;</sub> syntax, semantics, operations, embedding, quantifier rank, polarity |
| `InfinitaryLogic/Scott/` | Atomic diagrams, back-and-forth equivalence, Scott formulas/sentences, rank, height |
| `InfinitaryLogic/Karp/` | Karp&rsquo;s theorem and corollaries for countable structures |
| `InfinitaryLogic/Methods/Henkin/` | Consistency properties, Henkin construction, model existence, completeness; the countable-completion kernel |
| `InfinitaryLogic/Methods/Interpolation/` | Craig interpolation: the inseparability engine, the relationalization layer, PC separation |
| `InfinitaryLogic/Methods/WellOrdering/` | The well-ordering consistency property, boundedness, undefinability |
| `InfinitaryLogic/Methods/LopezEscobar/` | Query codes to PC classes: witness language, functional &Theta;, code class, disjointness, shared-symbol decoding |
| `InfinitaryLogic/Methods/EM/` | Indiscernible sequences, EM templates, EM realization |
| `InfinitaryLogic/ModelTheory/` | L&ouml;wenheim&ndash;Skolem, Hanf numbers, counting models, and the Craig / well-ordering facades |
| `InfinitaryLogic/Admissible/` | Admissible fragments (Fragment/Core, Fragment/Compact), Barwise compactness, proof system, Nadel bound |
| `InfinitaryLogic/Descriptive/` | Borel complexity of the structure space, the logic action and invariant &sigma;-algebras, counting dichotomy, L&oacute;pez&ndash;Escobar |
| `InfinitaryLogic/Conditional/` | The Silver chain and the Morley&ndash;Hanf discharge (both proved) |

## Resources

- [Blueprint (web)](https://cameronfreer.github.io/infinitary-logic/blueprint/) &middot; [Blueprint (pdf)](https://cameronfreer.github.io/infinitary-logic/blueprint/blueprint.pdf)
- [API docs](https://cameronfreer.github.io/infinitary-logic/docs/)
- [Dependency graph](https://cameronfreer.github.io/infinitary-logic/blueprint/dep_graph_document.html)

## References

- Barwise, J. (1975). *Admissible Sets and Structures*. Springer-Verlag.
- Karp, C. R. (1964). *Languages with Expressions of Infinite Length*. North-Holland.
- Karp, C. R. (1965). Finite-Quantifier Equivalence. In *The Theory of Models*, 407&ndash;412.
- Keisler, H. J. (1971). *Model Theory for Infinitary Logic*. North-Holland.
- Keisler, H. J. &amp; Knight, J. F. (2004). Barwise: Infinitary Logic and Admissible Sets. *Bulletin of Symbolic Logic*, 10(1), 4&ndash;36.
- L&oacute;pez-Escobar, E. G. K. (1965). An interpolation theorem for denumerably long formulas. *Fundamenta Mathematicae*, 57, 253&ndash;272.
- Marker, D. (2016). *Lectures on Infinitary Model Theory*. Cambridge University Press.
- Nadel, M. E. (1974). Scott sentences and admissible sets. *Annals of Mathematical Logic*, 7(2&ndash;3), 267&ndash;294.
