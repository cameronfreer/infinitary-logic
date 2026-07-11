import InfinitaryLogic.Core
import InfinitaryLogic.Countable
import InfinitaryLogic.Admissible
import InfinitaryLogic.Descriptive
import InfinitaryLogic.ModelTheory.MorleyHanf
import InfinitaryLogic.ModelTheory.HanfSpectrum
import InfinitaryLogic.ModelTheory.InfinitaryTypes
import InfinitaryLogic.ModelTheory.SmallModels
import InfinitaryLogic.ModelTheory.AElementary
import InfinitaryLogic.ModelTheory.FragmentLowenheimSkolem
import InfinitaryLogic.ModelTheory.AElementaryChains
import InfinitaryLogic.ModelTheory.TypeIsolation
import InfinitaryLogic.ModelTheory.CountableCompanion
import InfinitaryLogic.ModelTheory.TypePreservingBF
import InfinitaryLogic.ModelTheory.ArbitraryStabilization

/-!
# All: the sorry-free library surface

The default import surface, sorry-free, including the headline results: the Morley–Hanf
theorem (`morley_hanf`, exposed through the `ModelTheory/MorleyHanf.lean` facade — proved,
no hypotheses) and the Silver/Morley-counting chain. Excluded are only the legacy off-path
`Scott/Code.lean` (use `InfinitaryLogic.Everything` for it) and the WIP
frontier target.

## Targeted imports

- `InfinitaryLogic.Core`: syntax, semantics, Scott analysis, Karp's theorem
- `InfinitaryLogic.Countable`: model existence, LS, Hanf, counting, EM chain
- `InfinitaryLogic.Admissible`: admissible fragments, Barwise compactness
- `InfinitaryLogic.Descriptive`: descriptive set theory of model classes
- `InfinitaryLogic.ModelTheory.MorleyHanf`: the Morley–Hanf theorem and its corollaries
- `InfinitaryLogic.Everything`: all of the above plus the rest of `Conditional/` and the
  legacy off-path modules; WIP frontier modules under `Methods/` are excluded
  (see the `InfinitaryLogicWIP` target)
-/
