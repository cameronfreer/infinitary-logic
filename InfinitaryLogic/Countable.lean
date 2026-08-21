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
import InfinitaryLogic.Methods.EM.FragmentAdapter
import InfinitaryLogic.Methods.EM.TailAdapter

/-!
# Countable: model existence + model theory for countable structures

Import this bundle for the Henkin construction, model existence theorem,
Löwenheim-Skolem, Hanf numbers, counting models, and the EM-stretching chain
(indiscernibles → templates → realization).

The `_of_compact` endpoints (`Methods/EM/FragmentAdapter.lean` and the tail variants in
`TailAdapter.lean`) are now part of this bundle. They take a `Theoryω.OrdinaryCompactness`
oracle as a hypothesis and mention no admissible notion, so this bundle remains
admissible-free; the `_of_fragment` and `_of_fullFragment` endpoints they replaced are
deleted.
-/
