import InfinitaryLogic.Conditional.MorleyHanfTransfer
import InfinitaryLogic.Conditional.MorleyHanfSchemaDischarge
import InfinitaryLogic.Conditional.SilverBurgess
import InfinitaryLogic.Conditional.GandyHarrington
import InfinitaryLogic.Conditional.SilverCategoryRoute

/-!
# Conditional: theorems depending on external hypotheses or sorries

This bundle historically isolated results relying on external hypotheses or
sorries. The Silver chain here is now **sorry-free**; the directory remains
for the Morley–Hanf transfer hypotheses, the only genuinely conditional
content left.

## Contents

- `MorleyHanfTransfer.lean`: two forms of the Morley–Hanf bound.
  - Original bundled form: `MorleyHanfTransfer` hypothesis (Erdős-Rado +
    EM stretching, opaque) consumed by `morley_hanf_of_transfer`.
  - Split form (Phase 2 refactor): `MorleyHanfExtraction` (source-side
    residual — pairwise-distinct ℕ-indexed sequence restricted-indiscernible
    on a countable formula family) plus a per-target compactness oracle,
    joined by the **proved** bridge `hasArbLargeModels_of_restricted_extraction`.
    The EM stretching side is now fully formalized in
    `Methods/EM/FragmentAdapter.lean`, so only the extraction residual
    remains conditional.
- `SilverBurgess.lean`: Silver-Burgess splitting lemmas and `silver_core_closed`
  (sorry-free).
- `SilverCategoryRoute.lean`: Miller's classical category route, now **complete**:
  the hypothesis Props are all discharged (`mycielskiCantorHypothesis_holds`,
  `gSGraphHomHypothesis_holds` via the `G₀`-dichotomy fusion in
  `Descriptive/G0Fusion.lean`), so `gandy_harrington_of_gSGraphHom` is fed a proved
  input.
- `GandyHarrington.lean`: Silver-for-Borel, **PROVED** (2026-06-10, sorry-free):
  `gandy_harrington_for_relation`, `silver_core_polish`, `silverBurgessDichotomy`
  all report axioms exactly `[propext, Classical.choice, Quot.sound]`.

The only remaining `sorry` anywhere in the project is legacy, off-chain material in
`InfinitaryLogic/Combinatorics/ErdosRado.lean`.
-/
