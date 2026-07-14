import InfinitaryLogic.All
import InfinitaryLogic.Conditional
-- Legacy off-path modules (not reachable from the `All`/`Conditional` roots):
-- legacy FormulaCode API, superseded by the decoupled Scott pipeline
import InfinitaryLogic.Scott.Code
-- published backward-compatibility redirect (kept until a major release; built here so CI covers it)
import InfinitaryLogic.Basic

/-!
# Everything: the full library including conditional results and legacy modules

Imports ALL modules — the default surface (`InfinitaryLogic.All`), the
`Conditional/` bundle, and the legacy off-path `Scott/Code.lean` — and the
whole tree is **sorry-free**. (The exploratory all-arities Erdős–Rado ladder
`Combinatorics/ErdosRado.lean` was removed from the tree; it is preserved on
the `archive/legacy-erdos-rado` branch / `legacy-erdos-rado-final` tag. The
clean bounded Erdős–Rado chain — `PairErdosRadoGeneral`,
`EndHomogeneousErdosRado`, `FiniteArityErdosRadoInduction` — is on the
`InfinitaryLogicWIP` target and load-bearing for `morley_hanf`'s Marker
certification.) The only exclusion is the work-in-progress frontier under
`Methods/`, built by the separate non-default `InfinitaryLogicWIP` target.

The Silver chain in `Conditional/` is **sorry-free** (Silver's theorem
`gandy_harrington_for_relation` and the Silver–Burgess dichotomy
`silverBurgessDichotomy` are proved via the classical `G₀`-dichotomy
category route, with axioms exactly `[propext, Classical.choice,
Quot.sound]`). The Morley–Hanf theorem is likewise **unconditional**:
`morley_hanf` (`Conditional/MorleyHanfSchemaDischarge.lean`) — the residual
`MorleySeedTailTemplateRealizable` is proved by the schema-completion
construction, and the extraction side by `morleyHanfExtractionTail_holds`.

`InfinitaryLogic.All` remains the default bundle; it now includes the
Morley–Hanf facade and its supporting chain.
-/
