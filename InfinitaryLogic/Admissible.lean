import InfinitaryLogic.Admissible.Ackermann
import InfinitaryLogic.Admissible.Family
import InfinitaryLogic.Admissible.Theory
import InfinitaryLogic.Admissible.Ambient
import InfinitaryLogic.Admissible.AmbientHF
import InfinitaryLogic.Admissible.Numbering
import InfinitaryLogic.Admissible.Fragment
import InfinitaryLogic.Admissible.Fragment.Honest
import InfinitaryLogic.Admissible.HF
import InfinitaryLogic.Admissible.Barwise.Data
import InfinitaryLogic.Admissible.WithConstants
import InfinitaryLogic.Admissible.Compactness
import InfinitaryLogic.Admissible.Nadel
import InfinitaryLogic.Admissible.Barwise.ProofSystem
import InfinitaryLogic.Admissible.Barwise.Soundness
import InfinitaryLogic.Admissible.Barwise.HenkinClosed
import InfinitaryLogic.Admissible.Barwise.SourceFragment
import InfinitaryLogic.Admissible.Barwise.HenkinClosure
import InfinitaryLogic.Admissible.Barwise.GraphUniverse
import InfinitaryLogic.Admissible.Barwise.ConstantTransport

/-!
# Admissible: coded fragments, conditional compactness interfaces, proof system

Import this bundle for two distinct things.

**The honest coded-fragment interface** (`CodedFamily`, `Fragment/Honest`, `HF`): presentations and
certified coded families, a `Fragment` closed upward under exactly the families a presentation
names, and the HF instance — the first-order image inside `Lω₁ω` — whose compactness theorem is
*derived* from Mathlib's first-order compactness rather than assumed. Compactness is deliberately
not a field of any of these structures.

**The legacy scaffolding** (`Fragment`, `WithConstants`, `Compactness`, `Nadel`, and the
`Barwise/Data` presentation layer): conditional interfaces that package Barwise compactness and
the Nadel bound as hypotheses rather than discharging them. These are being replaced by the
interface above. The former consistency-property bridge is retired
(`docs/migration-consistency-bridge.md`).

**The proof system and the fair-enumeration adapters** (`Barwise/ProofSystem`, `Soundness`,
`HenkinClosed`, `SourceFragment`, `HenkinClosure`, `GraphUniverse`, `ConstantTransport`): the
surviving syntactic layer — derivability and soundness over a raw permitted sentence set, and the
countable-completion kernel adapters that give countable models of consistent theories in the
constants-expanded or graph universe.
The EM compactness-oracle layer is not part of this bundle: it assumes a
`Theoryω.OrdinaryCompactness` oracle and mentions no admissible notion, so it belongs to
`Countable` with the rest of the EM chain.
-/
