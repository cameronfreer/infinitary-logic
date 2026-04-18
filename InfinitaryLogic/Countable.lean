-- Model existence (Henkin construction)
import InfinitaryLogic.Methods.Henkin.ConsistencyProperty
import InfinitaryLogic.Methods.Henkin.Construction
import InfinitaryLogic.Methods.Henkin.ModelExistence
import InfinitaryLogic.Methods.Henkin.Completeness
import InfinitaryLogic.Methods.Henkin.SatisfiableConsistencyProperty

-- Model theory
import InfinitaryLogic.ModelTheory.LowenheimSkolem
import InfinitaryLogic.ModelTheory.Hanf
import InfinitaryLogic.ModelTheory.CountingModels

-- Ehrenfeucht–Mostowski chain
import InfinitaryLogic.Methods.EM.Indiscernible
import InfinitaryLogic.Methods.EM.Template
import InfinitaryLogic.Methods.EM.Realization
import InfinitaryLogic.Methods.EM.Extraction

-- Pure combinatorics (Erdős–Rado scaffolding)
import InfinitaryLogic.Combinatorics.ErdosRado

/-!
# Countable: model existence + model theory for countable structures

Import this bundle for the Henkin construction, model existence theorem,
Löwenheim-Skolem, Hanf numbers, counting models, and the EM-stretching chain
(indiscernibles → templates → realization).

The admissible-fragment adapter theorems (`_of_fragment`, `_of_fullFragment`,
`_of_compact`) are in `Methods/EM/FragmentAdapter.lean`, imported by the
`Admissible` bundle — NOT by this bundle. So `import InfinitaryLogic.Countable`
is genuinely countable-side only.
-/
