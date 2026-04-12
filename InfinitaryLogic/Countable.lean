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

/-!
# Countable: model existence + model theory for countable structures

Import this bundle for the Henkin construction, model existence theorem,
Löwenheim-Skolem, Hanf numbers, counting models, and the EM-stretching chain
(indiscernibles → templates → realization).

Note: the EM-realization file transitively imports some admissible-fragment
machinery (for the Barwise-wrapper endpoints); importing this bundle gives you
that material as well.
-/
