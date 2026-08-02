# Infinitary Logic in Lean 4

![CI](https://github.com/cameronfreer/infinitary-logic/actions/workflows/build.yml/badge.svg)
[![Latest release](https://img.shields.io/github/v/release/cameronfreer/infinitary-logic?label=release)](https://github.com/cameronfreer/infinitary-logic/releases/latest)

A Lean 4 formalization of infinitary logic (L∞ω and Lω₁ω), Scott sentences, and classical results in infinitary model theory, building on [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

- **[Project page](https://cameronfreer.github.io/infinitary-logic/)**
- **[Blueprint (web)](https://cameronfreer.github.io/infinitary-logic/blueprint/)** · **[Blueprint (pdf)](https://cameronfreer.github.io/infinitary-logic/blueprint/blueprint.pdf)**
- **[API docs](https://cameronfreer.github.io/infinitary-logic/docs/)** · **[Dependency graph](https://cameronfreer.github.io/infinitary-logic/blueprint/dep_graph_document.html)**
- **[Releases](https://github.com/cameronfreer/infinitary-logic/releases)** · **[How to cite](CITATION.cff)**

## Results

The [blueprint](https://cameronfreer.github.io/infinitary-logic/blueprint/) states these precisely and
narrates their proofs; this table names the endpoints and the hypotheses that matter.

### Scott analysis and Karp's theorem

| Result | In Lean | Scope |
|---|---|---|
| Every countable structure has a Scott sentence characterizing it up to isomorphism among countable structures | `scottSentence` | countable relational language |
| Scott rank is a countable ordinal | `scottRank` | |
| Back-and-forth equivalence at all ordinals characterizes L∞ω-equivalence | `karp_theorem_w` | |

### Model theory of Lω₁ω

| Result | In Lean | Scope |
|---|---|---|
| Model existence for consistency properties, with omitting types and Karp completeness | `model_existence` | countable language |
| ℶ_ω₁ is a Hanf bound for every Lω₁ω-sentence | `morley_hanf` | arbitrary language, no side hypotheses |
| The bound is sharp: Hanf(Lω₁ω) = ℶ_ω₁ | `Lomega1omegaHanfNumber_eq_beth_omega1` | |
| Models of every infinite size realizing only countably many complete types | `exists_small_model_of_hasArbLargeModels` | arbitrary languages |
| Small models lie in complete subclasses; κ-categorical sentences have κ-categorical complete completions | `exists_complete_sentence_of_lomega1omegaSmall`, `exists_complete_kCategorical_of_hasArbLargeModels` | countable relational vocabulary |

### Interpolation

All three are **sentence-level**. The theory-level analogues are false for Lω₁ω and are never claimed.

| Result | In Lean | Scope |
|---|---|---|
| **Craig** — interpolants whose function and relation symbols each lie in the intersection of the two roots' occurrence sets; also the PC-separation form | `craig_interpolation`, `craig_pcSeparation` | arbitrary language, no hypotheses |
| **Lyndon** — the polarity refinement: positively occurring relation symbols bounded by the roots' shared positive occurrences, negatively occurring ones by their shared negative occurrences | `lyndon_interpolation` | arbitrary language; **relation polarity, logical equality** — equality belongs to neither polarity class and is unconstrained, so López-Escobar's clause (.3) is *not* claimed |
| **Malitz** — the quantifier-class refinement: an entailment with universal consequent has a universal interpolant | `malitz_interpolation` | **universal consequent, relational language** of arbitrary cardinality |

### Definability and undefinability

| Result | In Lean | Scope |
|---|---|---|
| Chains of every countable length force a model carrying a relation-preserving map from ℚ (Marker 4.26) | `exists_model_relPreserving` | arbitrary language; raw positive form, **no injectivity claimed** |
| A uniform countable bound on the order types of well-ordered models (Marker 4.27) | `wellOrder_type_boundedness` | |
| No Lω₁ω-sentence has as models exactly the well-orders | `wellOrdering_undefinable` | |
| **López–Escobar** — a class of coded countable structures is Borel and isomorphism-invariant **iff** it is the model class of a single Lω₁ω-sentence; equivalently the invariant Borel classes are exactly the range of `ModelsOf` | `lopezEscobar_iff`, `lopezEscobar_action_iff` | **countable relational vocabulary** |
| The coded well-order class WO is not Borel in the logic space | `wellOrderClass_not_measurableSet` | the cheap half of Π¹₁-completeness; many-one hardness not claimed |

### Descriptive set theory

| Result | In Lean | Scope |
|---|---|---|
| **Silver's theorem** — a Borel equivalence relation on a Polish space has countably many classes or a perfect set of pairwise-inequivalent points | `gandy_harrington_for_relation` | via Miller's category route (G₀-dichotomy, Kuratowski–Ulam, Mycielski — all formalized here) |
| **The Silver–Burgess dichotomy** — on a standard Borel space the quotient is ≤ ℵ₀ or exactly 2^ℵ₀ | `silverBurgessDichotomy` | |
| **Morley counting** — countable models of an Lω₁ω-sentence number ≤ ℵ₁ or exactly 2^ℵ₀ | `morley_counting` | parametrized by the dichotomy, which this repository proves |
| Isomorphism is Borel under bounded Scott height | `iso_borel_of_bounded_scottHeight` | |

### Fragments and admissibility

An honest coded-fragment interface, with the HF fragment as its regression instance.

| Result | In Lean | Scope |
|---|---|---|
| **Coded-family presentations** — a family is a *code together with its decoding*, its index type supplied by the code and carrying an explicit `Encodable`, and its infinitary status a certificate the presentation grants | `AdmissiblePresentation`, `CodedFamily` | |
| **Honest coded closure** — a `Fragment` closed upward under exactly the families a presentation certifies, and under nothing else. Deliberately carries **no compactness data**: compactness is a theorem with hypotheses, not a field | `AdmissibleFragment` | |
| **The HF fragment** — the first-order image inside Lω₁ω, `L_HF = L_ωω`, as an instance with no adapter and no widening; its coded families are uninhabited, so both upward obligations are vacuous | `hfFragment`, `hfAdmissibleFragment` | sentence slice proved equal to `finitaryFragment` |
| **HF compactness**, *derived* from Mathlib's first-order compactness rather than assumed | `finitaryFragment_compact` | the semantic step is at `Language.{0,0}`; the syntax layer is universe-polymorphic |

**Barwise compactness and the Nadel bound are not proved**, and are not claimed. The interfaces
carrying them (`Admissible/Barwise/*`, `Admissible/Compactness.lean`, `Admissible/Nadel.lean`, and the
placeholders `AdmissibleFragmentCore.hf`, `FullBarwiseFragment`, `FiniteCompactFragment.CodedIn`) package a hypothesis rather
than discharging it, are labelled as such in source, and are being replaced by the interface above.
Progress is tracked in [#18](https://github.com/cameronfreer/infinitary-logic/issues/18)–[#20](https://github.com/cameronfreer/infinitary-logic/issues/20).
Malitz's relative preservation theorem (4.6) is likewise not proved
([#41](https://github.com/cameronfreer/infinitary-logic/issues/41)).

## Getting Started

```bash
git clone https://github.com/cameronfreer/infinitary-logic.git && cd infinitary-logic
lake build
```

To use in your own project, add the dependency to your `lakefile` and import a bundle:

```lean
import InfinitaryLogic.Core         -- syntax, semantics, Scott, Karp
import InfinitaryLogic.Countable    -- model existence, LS, Hanf, EM chain
import InfinitaryLogic.Admissible   -- coded-fragment interface, HF; legacy conditional interfaces
import InfinitaryLogic.Descriptive  -- descriptive set theory of model classes
import InfinitaryLogic.All          -- all of the above
import InfinitaryLogic.Conditional  -- Silver chain + Morley-Hanf theorem (both proved)
import InfinitaryLogic.Everything   -- everything including Conditional and legacy off-path modules
```

`import InfinitaryLogic` loads the default surface (`InfinitaryLogic.All`). Work-in-progress frontier
modules live in the separate non-default `InfinitaryLogicWIP` target, so they never enter it.

## Repository Guide

| Directory | Contents |
|---|---|
| `Linf/`, `Lomega1omega/` | the two syntaxes — formulas, semantics, operations, the embedding between them, countability predicates, quantifier rank |
| `Scott/`, `Karp/` | atomic diagrams, back-and-forth equivalence, Scott formulas and sentences, rank and height; Karp's theorem |
| `Methods/` | the proof engines: the Henkin/consistency-property kernel, interpolation, the well-ordering machine, López–Escobar, Ehrenfeucht–Mostowski |
| `ModelTheory/` | Löwenheim–Skolem, Hanf numbers and the Hanf spectrum, small models, counting |
| `Admissible/` | the coded-fragment interface and HF (above), plus the legacy conditional scaffolding |
| `Descriptive/` | the Borel structure space and a reusable descriptive-set-theory library — Cantor-antichain extraction, Mycielski, Kuratowski–Ulam, the G₀ dichotomy and fusion |
| `Combinatorics/` | infinite Ramsey and the bounded finite-arity Erdős–Rado chain |
| `Conditional/` | the Silver and Morley–Hanf chains, including the unconditional `morley_hanf` endpoint (the directory name is historical) |

## Verification

The tree is sorry-free, and the headline results depend on exactly `propext`, `Classical.choice` and
`Quot.sound`. CI builds the public and frontier targets and enforces both the proof boundary and the
axiom boundary on every commit.

Three dependency-cone guards additionally certify *proof architecture*, where an axiom scan cannot
reach: that the Henkin route consumes no maximal-consistency machinery, that the Morley–Hanf cone
avoids the legacy Erdős–Rado ladder, and that HF compactness genuinely consumes Mathlib's compactness
theorem while touching none of the legacy admissible structures.

Operational notes on building and releasing are in
[`docs/build-and-release-notes.md`](docs/build-and-release-notes.md).

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
