import InfinitaryLogic.Admissible.Fragment
import InfinitaryLogic.Admissible.CodedFamily
import InfinitaryLogic.Admissible.Predicates
import InfinitaryLogic.Admissible.Fragment.Honest
import InfinitaryLogic.Admissible.HF
import InfinitaryLogic.Admissible.Barwise.Data
import InfinitaryLogic.Admissible.WithConstants
import InfinitaryLogic.Admissible.Compactness
import InfinitaryLogic.Admissible.Nadel
import InfinitaryLogic.Admissible.Barwise.ProofSystem
import InfinitaryLogic.Admissible.Barwise.Soundness
import InfinitaryLogic.Admissible.Barwise.ConsistencyBridge
import InfinitaryLogic.Methods.EM.FragmentAdapter
import InfinitaryLogic.Methods.EM.TailAdapter

/-!
# Admissible: coded fragments, conditional compactness interfaces, proof system

Import this bundle for two distinct things.

**The honest coded-fragment interface** (`CodedFamily`, `Fragment/Honest`, `HF`): presentations and
certified coded families, a `Fragment` closed upward under exactly the families a presentation
names, and the HF instance — the first-order image inside `Lω₁ω` — whose compactness theorem is
*derived* from Mathlib's first-order compactness rather than assumed. Compactness is deliberately
not a field of any of these structures.

**The legacy scaffolding** (`Fragment`, `Barwise/*`, `WithConstants`, `Compactness`, `Nadel`):
conditional interfaces that package Barwise compactness and the Nadel bound as hypotheses rather
than discharging them, plus proof system / derivability, soundness, and the consistency-property
bridge. These are being replaced by the interface above.
The EM adapter theorems (`Methods/EM/FragmentAdapter.lean` and the
tail-indiscernibility variants in `Methods/EM/TailAdapter.lean`) live here
rather than in `Countable`, keeping that bundle admissible-free.
-/
