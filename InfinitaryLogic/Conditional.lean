import InfinitaryLogic.Conditional.MorleyHanfTransfer
import InfinitaryLogic.Conditional.MorleyHanfSchemaDischarge
import InfinitaryLogic.Conditional.SilverBurgess
import InfinitaryLogic.Conditional.GandyHarrington
import InfinitaryLogic.Conditional.SilverCategoryRoute

/-!
# Conditional: historically hypothesis-relative results, now discharged

This bundle historically isolated results relying on external hypotheses or
sorries. Both chains here are now **proved**: the Silver chain is sorry-free,
and the Morley–Hanf theorem is unconditional (`morley_hanf` in
`MorleyHanfSchemaDischarge.lean`). The directory name is retained for
stability; its hypothesis-relative theorems remain as transparent
intermediates and historical statement shapes.

## Contents

- `MorleyHanfTransfer.lean`: the Morley–Hanf reduction chain — the historical
  bundled form (`MorleyHanfTransfer` hypothesis, `morley_hanf_of_transfer`),
  the split bridges through `MorleyHanfExtraction` (a residual since shown
  false in ZFC) and its proved tail weakening `morleyHanfExtractionTail_holds`,
  and the realizability-relative endpoints over
  `MorleySeedTailTemplateRealizable`.
- `MorleyHanfSchemaDischarge.lean`: `MorleySeedTailTemplateRealizable` is
  **PROVED** via the schema-completion construction, and the definitive
  endpoint **`morley_hanf`** — `ℶ_ω₁` is a Hanf bound for every `L_ω₁ω`
  sentence, over an arbitrary language, with no hypotheses.
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
