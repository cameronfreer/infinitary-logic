import InfinitaryLogic.Core
import InfinitaryLogic.Countable
import InfinitaryLogic.Admissible
import InfinitaryLogic.Descriptive

/-!
# All: the sorry-free library surface

Imports everything EXCEPT the `Conditional` bundle (which contains results
depending on external hypotheses or the remaining sorry). Use
`InfinitaryLogic.Everything` if you want Conditional included.

## Targeted imports

- `InfinitaryLogic.Core`: syntax, semantics, Scott analysis, Karp's theorem
- `InfinitaryLogic.Countable`: model existence, LS, Hanf, counting, EM chain
- `InfinitaryLogic.Admissible`: admissible fragments, Barwise compactness
- `InfinitaryLogic.Descriptive`: descriptive set theory of model classes
- `InfinitaryLogic.Conditional`: results with external hypotheses or sorries
- `InfinitaryLogic.Everything`: all of the above including Conditional
-/
