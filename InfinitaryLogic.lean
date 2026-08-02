import InfinitaryLogic.All

/-!
# Infinitary Logic

A formalization of infinitary logic and its model theory:

* **L∞ω** — arbitrary conjunctions and disjunctions, indexed by an arbitrary type;
* **Lω₁ω** — the countable fragment, with ℕ-indexed connectives;
* **Scott analysis** — Scott formulas, sentences, rank and height, and Karp's theorem;
* the classical model theory built on them — model existence, Hanf numbers, interpolation,
  definability, and the descriptive set theory of model classes.

Statements, proof narratives and the dependency graph live in the
[blueprint](https://cameronfreer.github.io/infinitary-logic/blueprint/); declaration-level
documentation is in the [API docs](https://cameronfreer.github.io/infinitary-logic/docs/); the
[README](https://github.com/cameronfreer/infinitary-logic#readme) tabulates the results and their
hypotheses. Those are the places to look — this file deliberately keeps no inventory of its own, so
there is nothing here to drift out of date.

## Import bundles

`import InfinitaryLogic` loads the default surface (`InfinitaryLogic.All`). For narrower entry
points:

* `InfinitaryLogic.Core` — syntax, semantics, Scott analysis, Karp's theorem
* `InfinitaryLogic.Countable` — model existence, Löwenheim–Skolem, Hanf, counting, the EM chain
* `InfinitaryLogic.Admissible` — the coded-fragment interface and HF, plus the legacy conditional
  Barwise/Nadel scaffolding they are replacing
* `InfinitaryLogic.Descriptive` — descriptive set theory of model classes
* `InfinitaryLogic.Conditional` — the Silver chain and the Morley–Hanf chain (both proved; the
  directory name is historical)
* `InfinitaryLogic.Everything` — the above together with the legacy off-path modules

Work-in-progress frontier modules live in the separate, non-default `InfinitaryLogicWIP` target and
never enter the default surface. `InfinitaryLogic/Basic.lean` is a deprecated redirect to `All`.

## Conditional variants

Several Scott-analysis results have `_of` variants taking `CountableRefinementHypothesis` as an
explicit hypothesis. The unconditional forms are recovered from `countableRefinementHypothesis`,
which is proved in `Scott/RefinementCount.lean` — the hypothesis is a proof-organization device, not
an open assumption.
-/
