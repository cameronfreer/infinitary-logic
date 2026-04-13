# Infinitary Logic in Lean 4

![CI](https://github.com/cameronfreer/infinitary-logic/actions/workflows/build.yml/badge.svg)

A Lean 4 formalization of infinitary logic (L∞ω and Lω₁ω), Scott sentences, and classical results in infinitary model theory, building on [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

- **[Project page](https://cameronfreer.github.io/infinitary-logic/)**
- **[Blueprint (web)](https://cameronfreer.github.io/infinitary-logic/blueprint/)** · **[Blueprint (pdf)](https://cameronfreer.github.io/infinitary-logic/blueprint/blueprint.pdf)**
- **[API docs](https://cameronfreer.github.io/infinitary-logic/docs/)** · **[Dependency graph](https://cameronfreer.github.io/infinitary-logic/blueprint/dep_graph_document.html)**

## Main Results

- **Scott sentences** — Every countable structure in a countable relational language has a Scott sentence characterizing it up to isomorphism among countable structures.
- **Scott rank < ω₁** — The Scott rank of any countable structure is a countable ordinal.
- **Karp's theorem** — Back-and-forth equivalence at all ordinals characterizes L∞ω elementary equivalence.
- **Model existence** — Every countable consistent set of Lω₁ω sentences in a countable language has a countable model (Henkin-style construction, omitting types, Karp completeness).

## Scope and Boundaries

The formalization currently covers L∞ω and Lω₁ω syntax and semantics, Scott analysis (atomic diagrams, back-and-forth equivalence, Scott formulas/sentences, height and rank), Karp's theorem and corollaries, model existence via consistency properties, downward Löwenheim–Skolem for Lω₁ω, Hanf numbers, admissible-fragment results (Barwise compactness, Nadel bound), descriptive set theory of the space of countable structures (Borel complexity of satisfaction, BF-equivalence, and isomorphism; counting dichotomy), and the Silver–Burgess dichotomy for equivalence relations (splitting lemma, Cantor scheme, Silver's theorem for closed relations).

Some results carry explicit hypotheses packaging external content not yet formalized: `morley_hanf_of_transfer` is conditional on `MorleyHanfTransfer` (Erdős–Rado / Ehrenfeucht–Mostowski machinery). The Silver–Burgess dichotomy (`silverBurgessDichotomy`) is proved modulo 1 sorry in `gandy_harrington_for_relation` (in `Conditional/GandyHarrington.lean`), which requires lightface/effective Gandy–Harrington topology not yet in Mathlib; `morley_counting` chains through this.

## Repository Guide

- `InfinitaryLogic/Linf/` — L∞ω syntax, semantics, operations, countability predicates, quantifier rank
- `InfinitaryLogic/Lomega1omega/` — Lω₁ω syntax, semantics, operations, embedding into L∞ω, quantifier rank
- `InfinitaryLogic/Scott/` — Atomic diagrams, back-and-forth equivalence, Scott formulas/sentences, rank, height (`Height/Defs`, `Height/CanonicalSentence`, `Height/RankBounds`)
- `InfinitaryLogic/Karp/` — Karp's theorem and corollaries for countable structures
- `InfinitaryLogic/Methods/Henkin/` — Consistency properties, Henkin construction, model existence, completeness, omitting types
- `InfinitaryLogic/Methods/EM/` — Indiscernible sequences, EM templates, EM realization
- `InfinitaryLogic/ModelTheory/` — Löwenheim–Skolem, Hanf numbers, counting models
- `InfinitaryLogic/Admissible/` — Admissible fragments (`Fragment/Core`, `Fragment/Compact`), Barwise compactness, literature-faithful interface (`Barwise/Data`), proof system, Nadel bound
- `InfinitaryLogic/Descriptive/` — Borel complexity of the structure space, satisfaction, isomorphism; counting dichotomy, finite-carrier analysis
- `InfinitaryLogic/Conditional/` — Results depending on external hypotheses or sorries: `MorleyHanfTransfer` (Erdős–Rado + EM), `SilverBurgess`, `GandyHarrington` (1 sorry in `gandy_harrington_for_relation`)

## Getting Started

```bash
git clone https://github.com/cameronfreer/infinitary-logic.git && cd infinitary-logic
lake build
```

To use in your own project, add the dependency to your `lakefile` and import a bundle:

```lean
import InfinitaryLogic.Core         -- syntax, semantics, Scott, Karp
import InfinitaryLogic.Countable    -- model existence, LS, Hanf, EM chain
import InfinitaryLogic.Admissible   -- admissible fragments, Barwise compactness
import InfinitaryLogic.Descriptive  -- descriptive set theory of model classes
import InfinitaryLogic.All          -- all of the above (sorry-free)
import InfinitaryLogic.Conditional  -- results with external hypotheses or sorries
import InfinitaryLogic.Everything   -- everything including Conditional
```

`import InfinitaryLogic` also loads everything. `InfinitaryLogic/Basic.lean` is a deprecated redirect to `All`.

### Key Declarations

- `BFEquiv` — Back-and-forth equivalence between tuples, indexed by ordinals
- `scottSentence` — The Scott sentence of a countable structure
- `scottRank` — The Scott rank (ordinal measuring complexity of a structure)
- `karp_theorem_w` — Karp's theorem (potential isomorphism ↔ L∞ω-equivalence)
- `model_existence` — Model existence for Lω₁ω consistency properties
- `counting_coded_models_dichotomy` — Counting dichotomy for coded ℕ-models (conditional on `SilverBurgessDichotomy`)
- `morley_counting` — Morley's counting theorem: ≤ ℵ₁ or 2^ℵ₀ iso classes of countable models (conditional on `SilverBurgessDichotomy`)
- `iso_borel_of_bounded_scottHeight` — Isomorphism is Borel under bounded Scott height

## References

- Barwise, J. (1975). *Admissible Sets and Structures*. Springer-Verlag.
- Karp, C. R. (1964). *Languages with Expressions of Infinite Length*. North-Holland.
- Karp, C. R. (1965). Finite-Quantifier Equivalence. In *The Theory of Models*, 407–412.
- Keisler, H. J. (1971). *Model Theory for Infinitary Logic*. North-Holland.
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
