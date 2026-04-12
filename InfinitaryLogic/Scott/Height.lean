import InfinitaryLogic.Scott.Height.Defs
import InfinitaryLogic.Scott.Height.CanonicalSentence
import InfinitaryLogic.Scott.Height.RankBounds

/-!
# Scott Height and Canonical Scott Sentence

This module re-exports the three components of the Scott height analysis:

- `Scott.Height.Defs`: `scottHeight` definition and core properties
  (stabilization, invariance under isomorphism, `scottHeight < ω₁`).
- `Scott.Height.CanonicalSentence`: `canonicalScottSentence` definition and
  characterization theorems (potential isomorphism, isomorphism for countable
  structures, equivalence to the standard Scott sentence, quantifier rank bound).
- `Scott.Height.RankBounds`: `sr` (element rank supremum without +1),
  `AttainedScottRank`, and bounds relating `sr`, `scottRank`, and `scottHeight`.

## References

- [KK04], §1.3
- [Mar16]
-/
