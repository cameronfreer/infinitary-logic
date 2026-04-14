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
- `GandyHarrington.lean`: Silver-for-Borel via `gandy_harrington_for_relation`
  (1 remaining sorry: boldface Silver-for-Borel DST — Kuratowski–Ulam + Banach–Mazur
  games, or lightface Gandy–Harrington — not yet in mathlib). Downstream
  `silver_core_polish` and `silverBurgessDichotomy` chain through this sorry.
-/
