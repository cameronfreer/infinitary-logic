---
---

A Lean 4 formalization of **infinitary logic** (L<sub>&infin;&omega;</sub> and L<sub>&omega;<sub>1</sub>&omega;</sub>), **Scott sentences**, and classical results in infinitary model theory, building on [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

## Main Results

- **Scott sentences** &mdash; Every countable structure in a countable relational language has a Scott sentence characterizing it up to isomorphism among countable structures.
- **Scott rank < &omega;<sub>1</sub>** &mdash; The Scott rank of any countable structure is a countable ordinal.
- **Karp's theorem** &mdash; Back-and-forth equivalence at all ordinals characterizes L<sub>&infin;&omega;</sub> elementary equivalence.
- **Model existence** &mdash; Every countable consistent set of L<sub>&omega;<sub>1</sub>&omega;</sub> sentences in a countable language has a countable model (Henkin-style construction, omitting types, Karp completeness).

## Scope

The formalization currently covers:

- **L<sub>&infin;&omega;</sub> infrastructure** &mdash; syntax (`BoundedFormulaInf` with arbitrary index types for conjunctions/disjunctions), semantics, quantifier rank, and conversions between L<sub>&infin;&omega;</sub> and L<sub>&omega;<sub>1</sub>&omega;</sub>.
- **Scott analysis** &mdash; atomic diagrams, back-and-forth equivalence indexed by ordinals, Scott formulas/sentences, Scott height and rank, and the countable refinement hypothesis.
- **Karp's theorem** &mdash; potential isomorphisms, the main equivalence (`karp_theorem_w`), and corollaries for countable structures.
- **Model existence** &mdash; consistency properties, Henkin construction, truth lemma, model existence theorem, Karp completeness, and omitting types.
- **Further model theory** &mdash; downward L&ouml;wenheim&ndash;Skolem for L<sub>&omega;<sub>1</sub>&omega;</sub>, Hanf numbers, conditional Morley&ndash;Hanf bound (conditional on `MorleyHanfTransfer`), and counting models (Morley counting theorem: &le; &alefsym;<sub>1</sub> or 2<sup>&alefsym;<sub>0</sub></sup> iso classes).
- **Silver&ndash;Burgess dichotomy** &mdash; splitting lemma, Cantor scheme, Silver&rsquo;s theorem for closed equivalence relations on Polish spaces, and `silverBurgessDichotomy` (1 sorry: `gandy_harrington_for_relation` in `Conditional/GandyHarrington.lean`).
- **Admissible fragments** &mdash; Barwise compactness, Barwise completeness II, and the Nadel bound.

Some results carry explicit hypotheses that package external mathematical content not yet formalized (e.g., `MorleyHanfTransfer` for Erd&#337;s&ndash;Rado / Ehrenfeucht&ndash;Mostowski machinery, `SilverBurgessDichotomy` for the Silver&ndash;Burgess dichotomy).

## Import Bundles

| Bundle | Contents |
|--------|----------|
| `InfinitaryLogic.Core` | Syntax, semantics, Scott analysis, Karp&rsquo;s theorem |
| `InfinitaryLogic.Countable` | Model existence, L&ouml;wenheim&ndash;Skolem, Hanf, counting, EM chain |
| `InfinitaryLogic.Admissible` | Admissible fragments, Barwise compactness, proof system |
| `InfinitaryLogic.Descriptive` | Descriptive set theory of model classes |
| `InfinitaryLogic.Conditional` | Results with external hypotheses or sorries |
| `InfinitaryLogic.All` | Everything (also available via `import InfinitaryLogic`) |

`InfinitaryLogic/Basic.lean` is a deprecated redirect to `All`.

## Components

| Directory | Contents |
|-----------|----------|
| `InfinitaryLogic/Linf/` | L<sub>&infin;&omega;</sub> syntax, semantics, operations, countability predicates, quantifier rank |
| `InfinitaryLogic/Lomega1omega/` | L<sub>&omega;<sub>1</sub>&omega;</sub> syntax, semantics, operations, embedding, quantifier rank |
| `InfinitaryLogic/Scott/` | Atomic diagrams, back-and-forth equivalence, Scott formulas/sentences, rank, height |
| `InfinitaryLogic/Karp/` | Karp&rsquo;s theorem and corollaries for countable structures |
| `InfinitaryLogic/Methods/Henkin/` | Consistency properties, Henkin construction, model existence, completeness |
| `InfinitaryLogic/Methods/EM/` | Indiscernible sequences, EM templates, EM realization |
| `InfinitaryLogic/ModelTheory/` | L&ouml;wenheim&ndash;Skolem, Hanf numbers, counting models |
| `InfinitaryLogic/Admissible/` | Admissible fragments (Fragment/Core, Fragment/Compact), Barwise compactness, proof system, Nadel bound |
| `InfinitaryLogic/Descriptive/` | Borel complexity of structure space, satisfaction, isomorphism; counting dichotomy, finite-carrier analysis |
| `InfinitaryLogic/Conditional/` | MorleyHanfTransfer, SilverBurgess, GandyHarrington (1 sorry in `gandy_harrington_for_relation`) |

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
- Marker, D. (2016). *Lectures on Infinitary Model Theory*. Cambridge University Press.
- Nadel, M. E. (1974). Scott sentences and admissible sets. *Annals of Mathematical Logic*, 7(2&ndash;3), 267&ndash;294.
