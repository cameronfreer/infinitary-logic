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
- **Silver's theorem & the Silver–Burgess dichotomy** — A Borel equivalence relation on a Polish space has countably many classes or a perfect set of pairwise-inequivalent points (`gandy_harrington_for_relation`); on a standard Borel space the quotient is ≤ ℵ₀ or exactly 2^ℵ₀ (`silverBurgessDichotomy`). Proved via Miller's classical category route: the Kechris–Solecki–Todorcevic G₀-dichotomy (positivity ideals, Lusin separation, fusion), Miller's G_S independence lemma, Kuratowski–Ulam, and Mycielski's theorem — all formalized here.
- **Morley counting** — The number of isomorphism classes of countable models of an Lω₁ω sentence is ≤ ℵ₁ or exactly 2^ℵ₀ (`morley_counting`, parametrized by the dichotomy; unconditional via `silverBurgessDichotomy`).

## Scope and Boundaries

The formalization currently covers L∞ω and Lω₁ω syntax and semantics, Scott analysis (atomic diagrams, back-and-forth equivalence, Scott formulas/sentences, height and rank), Karp's theorem and corollaries, model existence via consistency properties, downward Löwenheim–Skolem for Lω₁ω, Hanf numbers, admissible-fragment results (Barwise compactness, Nadel bound), descriptive set theory of the space of countable structures (Borel complexity of satisfaction, BF-equivalence, and isomorphism; counting dichotomy), and Silver's theorem with the Silver–Burgess dichotomy, **fully proved** via Miller's classical category route: Mycielski's theorem (`Descriptive/Mycielski.lean`), Kuratowski–Ulam (`Descriptive/KuratowskiUlam.lean`), the `G_S` graphs with Miller's independence lemma (`Descriptive/GSGraph.lean`), the KST separation core and positivity ideals (`Descriptive/G0Dichotomy.lean`), and the G₀-dichotomy fusion (`Descriptive/G0Fusion.lean`). The proof route is

> G₀ homomorphism → meager pullback sections → Kuratowski–Ulam → Mycielski → Silver → Silver–Burgess → Morley counting,

and the endpoints `gandy_harrington_for_relation`, `silverBurgessDichotomy`, and the `morley_counting` instantiation all have axioms exactly `[propext, Classical.choice, Quot.sound]`.

Some results carry explicit hypotheses packaging external content not yet formalized. For Morley–Hanf, two forms coexist: the original `morley_hanf_of_transfer` is conditional on the single opaque `MorleyHanfTransfer` hypothesis (bundling Erdős–Rado extraction and EM stretching), while the proved bridge `hasArbLargeModels_of_restricted_extraction` takes a smaller residual `MorleyHanfExtraction` (source-side only: pairwise-distinct ℕ-indexed sequence restricted-indiscernible on a countable formula family) plus a per-target compactness oracle — the EM stretching side is now fully formalized in `Methods/EM/FragmentAdapter.lean`.

## Repository Guide

- `InfinitaryLogic/Linf/` — L∞ω syntax, semantics, operations, countability predicates, quantifier rank
- `InfinitaryLogic/Lomega1omega/` — Lω₁ω syntax, semantics, operations, embedding into L∞ω, quantifier rank
- `InfinitaryLogic/Scott/` — Atomic diagrams, back-and-forth equivalence, Scott formulas/sentences, rank, height (`Height/Defs`, `Height/CanonicalSentence`, `Height/RankBounds`)
- `InfinitaryLogic/Karp/` — Karp's theorem and corollaries for countable structures
- `InfinitaryLogic/Methods/Henkin/` — Consistency properties, Henkin construction, model existence, completeness, omitting types
- `InfinitaryLogic/Methods/EM/` — Indiscernible sequences, EM templates, EM realization
- `InfinitaryLogic/ModelTheory/` — Löwenheim–Skolem, Hanf numbers, counting models
- `InfinitaryLogic/Admissible/` — Admissible fragments (`Fragment/Core`, `Fragment/Compact`), Barwise compactness, literature-faithful interface (`Barwise/Data`), proof system, Nadel bound
- `InfinitaryLogic/Descriptive/` — Borel complexity of the structure space, satisfaction, isomorphism; counting dichotomy, finite-carrier analysis; and a reusable DST library: Cantor-antichain extraction (`CantorAntichain`), Mycielski (`Mycielski`), Kuratowski–Ulam (`KuratowskiUlam`), the `G_S` graphs (`GSGraph`), and the classical G₀-dichotomy machinery (`G0Dichotomy`, `G0Fusion`)
- `InfinitaryLogic/Conditional/` — The Silver chain (`SilverBurgess`, `SilverCategoryRoute`, `GandyHarrington` — now sorry-free) and `MorleyHanfTransfer`, the one remaining genuinely conditional result (original bundled `MorleyHanfTransfer` hypothesis + split residual `MorleyHanfExtraction` with proved `hasArbLargeModels_of_restricted_extraction` bridge)

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
import InfinitaryLogic.Conditional  -- Silver chain (sorry-free) + Morley-Hanf transfer hypotheses
import InfinitaryLogic.Everything   -- everything including Conditional and legacy off-path modules
```

`import InfinitaryLogic` now loads the sorry-free surface (`InfinitaryLogic.All`); use `import InfinitaryLogic.Everything` if you want `Conditional/` and the legacy off-path modules (`Scott/Code.lean`, the sorry-bearing `Combinatorics/ErdosRado.lean` scaffolding) included — work-in-progress frontier modules under `Methods/` are excluded and live in the separate non-default `InfinitaryLogicWIP` target. `InfinitaryLogic/Basic.lean` is a deprecated redirect to `All`.

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
- `erdos_rado_pair_omega1` — The Erdős–Rado pair partition relation at ω₁ used by the EM chain
- `hasArbLargeModels_of_restricted_extraction` — Proved Morley–Hanf bridge: restricted source-side extraction + per-target compactness ⇒ arbitrarily large models

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
