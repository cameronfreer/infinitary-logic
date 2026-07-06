import InfinitaryLogic.All
import InfinitaryLogic.Conditional
-- Legacy off-path modules (not reachable from the `All`/`Conditional` roots):
-- legacy FormulaCode API, superseded by the decoupled Scott pipeline
import InfinitaryLogic.Scott.Code
-- legacy sorry-bearing Erdős–Rado scaffolding, off the critical path
import InfinitaryLogic.Combinatorics.ErdosRado

/-!
# Everything: the full library including conditional results and legacy modules

Imports ALL modules: the sorry-free surface (`InfinitaryLogic.All`), the
`Conditional/` bundle, and the legacy off-path modules (`Scott/Code.lean`,
the sorry-bearing `Combinatorics/ErdosRado.lean` scaffolding). The only
exclusion is the work-in-progress frontier under `Methods/` (the Skolem
towers and the EM term model), which is built by the separate non-default
`InfinitaryLogicWIP` target.

The Silver chain in `Conditional/` is **sorry-free** (Silver's theorem
`gandy_harrington_for_relation` and the Silver–Burgess dichotomy
`silverBurgessDichotomy` are proved via the classical `G₀`-dichotomy
category route, with axioms exactly `[propext, Classical.choice,
Quot.sound]`). The remaining conditional content is the Morley–Hanf
transfer, now reduced to the single residual
`MorleySeedTailTemplateRealizable` (consumed by
`morley_hanf_of_tail_realizable`; the extraction side is discharged by
`morleyHanfExtractionTail_holds`).

`InfinitaryLogic.All` remains the sorry-free bundle without `Conditional/`
or the legacy modules.
-/
