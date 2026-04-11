-- Model existence (Henkin construction)
import InfinitaryLogic.ModelExistence.ConsistencyProperty
import InfinitaryLogic.ModelExistence.HenkinConstruction
import InfinitaryLogic.ModelExistence.Theorem
import InfinitaryLogic.ModelExistence.Completeness
import InfinitaryLogic.ModelExistence.SatisfiableConsistencyProperty

-- Model theory
import InfinitaryLogic.ModelTheory.LowenheimSkolem
import InfinitaryLogic.ModelTheory.Hanf
import InfinitaryLogic.ModelTheory.CountingModels

-- Ehrenfeucht–Mostowski chain
import InfinitaryLogic.ModelTheory.Indiscernible
import InfinitaryLogic.ModelTheory.EMTemplate
import InfinitaryLogic.ModelTheory.EMRealization

/-!
# Countable: model existence + model theory for countable structures

Import this bundle for the Henkin construction, model existence theorem,
Löwenheim-Skolem, Hanf numbers, counting models, and the EM-stretching chain
(indiscernibles → templates → realization).

Note: the EM-realization file transitively imports some admissible-fragment
machinery (for the Barwise-wrapper endpoints); importing this bundle gives you
that material as well.
-/
