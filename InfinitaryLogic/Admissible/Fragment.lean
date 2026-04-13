import InfinitaryLogic.Admissible.Fragment.Core
import InfinitaryLogic.Admissible.Fragment.Compact

/-!
# Admissible Fragments

Re-exports the two layers of the admissible fragment interface:

- `Fragment.Core`: `AdmissibleFragmentCore` — syntactic closure properties only
  (formulas, height, closure under connectives, sub-formula backward closures).
  The stable interface layer for proof system, soundness, Nadel bound.

- `Fragment.Compact`: `FiniteCompactFragment` — extends Core with a finite-subset
  compactness axiom (HF-style, stronger than the standard Barwise theorem).
  Includes `AFinite`. Retained for backward compatibility.

See `BarwiseCompactnessData` (in `Barwise/Data.lean`) for the literature-faithful
Barwise compactness interface.

## References

- [KK04], §3
- [Bar75], Ch. III, VII–VIII
-/
