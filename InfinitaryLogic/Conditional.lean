import InfinitaryLogic.Conditional.MorleyHanfTransfer
import InfinitaryLogic.Conditional.SilverBurgess
import InfinitaryLogic.Conditional.GandyHarrington

/-!
# Conditional: theorems depending on external hypotheses or sorries

This bundle isolates results that rely on hypotheses not yet internalized
or on remaining sorry boundaries. Placing them in `Conditional/` makes
the external dependency visible at the directory level.

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
- `SilverBurgess.lean`: Silver-Burgess dichotomy (sorry-free splitting lemmas,
  but the endpoint `silverBurgessDichotomy` chains through the GH sorry).
- `GandyHarrington.lean`: Silver-for-Borel via `gandy_harrington_for_relation`
  (1 remaining sorry: boldface Silver-for-Borel DST — Kuratowski–Ulam + Banach–Mazur
  games, or lightface Gandy–Harrington — not yet in mathlib). Downstream
  `silver_core_polish` and `silverBurgessDichotomy` chain through this sorry.
-/
