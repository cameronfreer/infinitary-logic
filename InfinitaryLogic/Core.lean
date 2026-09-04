import InfinitaryLogic.Util

-- L∞ω (arbitrary infinitary logic)

-- Lω₁ω (countable infinitary logic)
import InfinitaryLogic.Lomega1omega.Syntax
import InfinitaryLogic.Lomega1omega.Semantics
import InfinitaryLogic.Lomega1omega.CountableIndex
import InfinitaryLogic.Lomega1omega.Fragment
import InfinitaryLogic.Lomega1omega.NegationClosure
import InfinitaryLogic.Lomega1omega.Operations
import InfinitaryLogic.Lomega1omega.Theory
import InfinitaryLogic.Lomega1omega.Entailment
import InfinitaryLogic.Lomega1omega.QuantifierRank
import InfinitaryLogic.Lomega1omega.FiniteQuantification
import InfinitaryLogic.Lomega1omega.Depth
import InfinitaryLogic.Lomega1omega.InfiniteAxiom
import InfinitaryLogic.Lomega1omega.Polarity
import InfinitaryLogic.Lomega1omega.PolaritySemantics
import InfinitaryLogic.Lomega1omega.QuantifierClass
import InfinitaryLogic.Lomega1omega.QuantifierSemantics
import InfinitaryLogic.Lomega1omega.QuantifierOccurrence

-- Scott sentences and ranks
import InfinitaryLogic.Scott.AtomicDiagram
import InfinitaryLogic.Scott.BackAndForth
import InfinitaryLogic.Scott.Stabilization
import InfinitaryLogic.Scott.Formula
import InfinitaryLogic.Scott.Sentence
import InfinitaryLogic.Scott.RefinementCount
import InfinitaryLogic.Scott.Rank
import InfinitaryLogic.Scott.QuantifierRank
import InfinitaryLogic.Scott.Height

-- Karp's theorem
import InfinitaryLogic.Karp.PotentialIso
import InfinitaryLogic.Karp.CarrierTheorem
import InfinitaryLogic.Karp.CountableCorollary

/-!
# Core: syntax, semantics, Scott analysis, and Karp's theorem

Import this bundle for the foundational objects of infinitary logic without
model-existence machinery, admissible-set theory, or descriptive set theory.

## One syntax, fixed at a branching carrier

The infinitary syntax comes from the pinned Mathlib dependency. It is **proposed
upstream, not yet accepted** — the pin is a fork branch, and names or packaging may
change under review. Project-level facades (`Lomega1omega/Syntax.lean`,
`Semantics.lean`, `QuantifierRank.lean`, `CountableIndex.lean`, and
`Karp/CarrierTheorem.lean`) exist so that such a change is absorbed there rather
than across the theorem files.

There is a single infinitary syntax, `BoundedFormulaInf ι α n`, whose
`iSup`/`iInf` nodes branch over a carrier `ι` fixed once for the whole formula
rather than chosen at each node. L∞ω is that type at an arbitrary carrier; Lω₁ω
is the same type at carrier `ℕ`:

```
L.BoundedFormulaω α n  =  L.BoundedFormulaInf ℕ α n     -- definitional
L.Sentenceω            =  L.SentenceInf ℕ               -- definitional
LomegaEquiv L M N      =  InfEquivAt L ℕ M N            -- definitional
```

So embedding Lω₁ω into L∞ω is **not an operation**: it is specialization at
carrier `ℕ`, and every ω-level statement is already an L∞ω statement. `Lomega1omega/`
re-exports the `ℕ` specialization under ω-facing names — `@[match_pattern]` abbrevs
for the constructors, so `match`/`induction` keep working — and adds what is genuinely
ω-specific (fragments, polarity, quantifier classes, the `Encodable` adapters).

Transport between carriers is a first-class operation instead: `IndexCoding ι κ`
reindexes a formula from one carrier to another, padding undecodable branches with
`⊥`/`⊤`. That is what lets Karp's theorem be stated at an arbitrary common carrier
(`karp_theorem_at`) with the canonical sum carrier as a corollary
(`karp_theorem_on_sum`); see `Karp/CarrierTheorem.lean`.
-/
