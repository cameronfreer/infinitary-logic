import InfinitaryLogic.Conditional.MorleyHanfTransfer
import InfinitaryLogic.Conditional.SilverBurgess
import InfinitaryLogic.Conditional.GandyHarrington

/-!
# Conditional: theorems depending on external hypotheses or sorries

This bundle isolates results that rely on hypotheses not yet internalized
or on remaining sorry boundaries. Placing them in `Conditional/` makes
the external dependency visible at the directory level.

## Contents

- `MorleyHanfTransfer.lean`: `MorleyHanfTransfer` hypothesis (Erdős-Rado +
  EM stretching) and `morley_hanf_of_transfer` conditional theorem.
- `SilverBurgess.lean`: Silver-Burgess dichotomy (sorry-free splitting lemmas,
  but the endpoint `silverBurgessDichotomy` chains through the GH sorry).
- `GandyHarrington.lean`: Gandy-Harrington topology and `gandy_harrington_for_relation`
  (1 sorry: `silver_core_polish`, requiring lightface/effective DST).
-/
