---
---

A Lean 4 formalization of **infinitary logic** (L<sub>&infin;&omega;</sub> and L<sub>&omega;<sub>1</sub>&omega;</sub>) and its model theory, building on [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

## Status

**Sorry-free**, with every headline result depending on exactly the three standard axioms `propext`, `Classical.choice`, `Quot.sound`. See the [latest release](https://github.com/cameronfreer/infinitary-logic/releases/latest).

## Headline results

- **Scott analysis and Karp's theorem** &mdash; every countable structure has a Scott sentence characterizing it up to isomorphism; Scott rank is a countable ordinal; back-and-forth equivalence at all ordinals characterizes L<sub>&infin;&omega;</sub>-equivalence.
- **Model existence and L&ouml;wenheim&ndash;Skolem** &mdash; consistency properties, the Henkin construction, omitting types, Karp completeness, and downward L&ouml;wenheim&ndash;Skolem in both the sentence and fragment-elementary forms.
- **Hanf numbers** &mdash; &beth;<sub>&omega;<sub>1</sub></sub> is a Hanf bound for every L<sub>&omega;<sub>1</sub>&omega;</sub>-sentence over an arbitrary language, with no side hypotheses, and it is sharp: Hanf(L<sub>&omega;<sub>1</sub>&omega;</sub>) = &beth;<sub>&omega;<sub>1</sub></sub>.
- **Small models, complete sentences, categoricity** &mdash; models of every infinite size realizing countably many types; small models lie in complete subclasses; &kappa;-categorical sentences have &kappa;-categorical complete completions.
- **Craig, Lyndon and Malitz interpolation** &mdash; sharp shared-vocabulary interpolants over **arbitrary** languages, with the PC-separation form; and their polarity refinement, in which the interpolant's positively (negatively) occurring relation symbols are bounded by the roots' positive (negative) occurrences, equality being logical and unconstrained; and Malitz's quantifier-class refinement, in which an entailment with universal consequent has a universal interpolant.
- **Well-ordering** &mdash; a uniform countable bound on the order types of well-ordered models (Marker 4.27); no sentence defines the class of well-orders; and the coded well-order class is **not Borel**.
- **Descriptive set theory** &mdash; the standard Borel structure space, Silver's theorem and the Silver&ndash;Burgess dichotomy (via Miller's category route, formalized here), and Morley counting.
- **The L&oacute;pez&ndash;Escobar theorem** &mdash; a class of coded countable structures is Borel and isomorphism-invariant **iff** it is the model class of a single L<sub>&omega;<sub>1</sub>&omega;</sub>-sentence; equivalently, the invariant Borel classes are exactly the range of `ModelsOf`.

## Documentation

- [README](https://github.com/cameronfreer/infinitary-logic#readme) &mdash; precise statements, proof routes, import bundles, and the directory layout
- [Blueprint (web)](https://cameronfreer.github.io/infinitary-logic/blueprint/) &middot; [Blueprint (pdf)](https://cameronfreer.github.io/infinitary-logic/blueprint/blueprint.pdf) &middot; [Dependency graph](https://cameronfreer.github.io/infinitary-logic/blueprint/dep_graph_document.html)
- [API docs](https://cameronfreer.github.io/infinitary-logic/docs/)
- [Releases](https://github.com/cameronfreer/infinitary-logic/releases) &middot; [How to cite](https://github.com/cameronfreer/infinitary-logic/blob/master/CITATION.cff)

*Scope, component-by-component contents, and proof-route narratives are maintained in the README only, so they cannot drift out of sync here.*
