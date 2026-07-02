import InfinitaryLogic.Core
import InfinitaryLogic.Countable
import InfinitaryLogic.Admissible
import InfinitaryLogic.Descriptive

/-!
# All: the sorry-free library surface

Imports everything EXCEPT the `Conditional` bundle (results depending on
external hypotheses) and the legacy off-path modules (`Scott/Code.lean`,
`Combinatorics/ErdosRado.lean`). Use `InfinitaryLogic.Everything` if you
want those included.

## Targeted imports

- `InfinitaryLogic.Core`: syntax, semantics, Scott analysis, Karp's theorem
- `InfinitaryLogic.Countable`: model existence, LS, Hanf, counting, EM chain
- `InfinitaryLogic.Admissible`: admissible fragments, Barwise compactness
- `InfinitaryLogic.Descriptive`: descriptive set theory of model classes
- `InfinitaryLogic.Conditional`: results with external hypotheses
- `InfinitaryLogic.Everything`: all of the above plus Conditional and the
  legacy off-path modules (not sorry-free); WIP frontier modules under
  `Methods/` are excluded (see the `InfinitaryLogicWIP` target)
-/
