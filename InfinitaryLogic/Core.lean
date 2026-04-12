import InfinitaryLogic.Util

-- L∞ω (arbitrary infinitary logic)
import InfinitaryLogic.Linf.Syntax
import InfinitaryLogic.Linf.Semantics
import InfinitaryLogic.Linf.Operations
import InfinitaryLogic.Linf.Countability
import InfinitaryLogic.Linf.Theory
import InfinitaryLogic.Linf.QuantifierRank

-- Lω₁ω (countable infinitary logic)
import InfinitaryLogic.Lomega1omega.Syntax
import InfinitaryLogic.Lomega1omega.Semantics
import InfinitaryLogic.Lomega1omega.Operations
import InfinitaryLogic.Lomega1omega.Embedding
import InfinitaryLogic.Lomega1omega.Theory
import InfinitaryLogic.Lomega1omega.QuantifierRank

-- Scott sentences and ranks
import InfinitaryLogic.Scott.AtomicDiagram
import InfinitaryLogic.Scott.BackAndForth
import InfinitaryLogic.Scott.Formula
import InfinitaryLogic.Scott.Sentence
import InfinitaryLogic.Scott.RefinementCount
import InfinitaryLogic.Scott.Rank
import InfinitaryLogic.Scott.QuantifierRank
import InfinitaryLogic.Scott.Height

-- Karp's theorem
import InfinitaryLogic.Karp.PotentialIso
import InfinitaryLogic.Karp.Theorem
import InfinitaryLogic.Karp.CountableCorollary

/-!
# Core: syntax, semantics, Scott analysis, and Karp's theorem

Import this bundle for the foundational objects of infinitary logic without
model-existence machinery, admissible-set theory, or descriptive set theory.

## Linf / Lomega1omega parallel structure

`Linf/` and `Lomega1omega/` have a deliberately parallel file structure
(Syntax, Semantics, Operations, Theory, QuantifierRank) with consistent
theorem names (`realize_imp`, `realize_iSup`, `realize_iInf`, etc.). The
fundamental difference is the connective index type:

- **Linf**: `iSup {ι : Type uι} (φs : ι → ...)` — arbitrary index types
- **Lomega1omega**: `iSup (φs : ℕ → ...)` — ℕ-indexed only

This difference is baked into the inductive type constructors
(`BoundedFormulaInf` vs `BoundedFormulaω`), so a shared abstract kernel
would require type-level parametrization over the index type — feasible
but non-trivial. The current parallel structure trades ~1000 lines of
duplication for clarity and type safety. The embedding
(`Lomega1omega/Embedding.lean`) maps between the two logics.
-/
