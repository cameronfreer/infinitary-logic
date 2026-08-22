-- Structure space and measurability
import InfinitaryLogic.Descriptive.StructureSpace
import InfinitaryLogic.Descriptive.Measurable
import InfinitaryLogic.Descriptive.Topology
import InfinitaryLogic.Descriptive.Polish
import InfinitaryLogic.Descriptive.CodeTransport

-- Satisfaction and equivalence Borel complexity
import InfinitaryLogic.Descriptive.SatisfactionBorel
import InfinitaryLogic.Descriptive.LopezEscobarEasy
import InfinitaryLogic.Descriptive.QueryCode
import InfinitaryLogic.Descriptive.AnalyticTree
import InfinitaryLogic.Descriptive.SatisfactionBorelOn
import InfinitaryLogic.Descriptive.BFEquivBorel
import InfinitaryLogic.Descriptive.IsomorphismBorel
import InfinitaryLogic.Descriptive.ModelClassStandardBorel

-- Cantor scheme / perfect antichain extraction (pure Mathlib infrastructure)
import InfinitaryLogic.Descriptive.CantorAntichain
import InfinitaryLogic.Descriptive.PerfectAntichain
import InfinitaryLogic.Descriptive.StructureIsoSetoid
import InfinitaryLogic.Descriptive.RankedThinness
import InfinitaryLogic.Descriptive.Mycielski
import InfinitaryLogic.Descriptive.KuratowskiUlam
import InfinitaryLogic.Descriptive.GSGraph
import InfinitaryLogic.Descriptive.G0Dichotomy
import InfinitaryLogic.Descriptive.G0Fusion

-- Counting dichotomy and finite carrier
import InfinitaryLogic.Descriptive.CountingDichotomy
import InfinitaryLogic.Descriptive.FiniteCarrier

-- The pointwise-convergence topology on S∞ = Equiv.Perm ℕ (issue #27)
import InfinitaryLogic.Descriptive.PermTopology
import InfinitaryLogic.Descriptive.PermPolishGroup

-- The S∞ = Equiv.Perm ℕ action on the structure space (algebraic layer, issue #27)
import InfinitaryLogic.Descriptive.LogicAction

-- The jointly-continuous Polish S∞-action on the structure space (issue #27)
import InfinitaryLogic.Descriptive.PolishAction

-- The invariant σ-algebras on the structure space (issue #28)
import InfinitaryLogic.Descriptive.InvariantMeasurableSpace
import InfinitaryLogic.Descriptive.InvariantMeasurableModels

-- The coded class of countable well-orders and its order-type supply (issue #33)
import InfinitaryLogic.Descriptive.WellOrderClass

-- THE LÓPEZ–ESCOBAR THEOREM: both packaged equivalences and the collection equality (issue #10)
import InfinitaryLogic.Descriptive.LopezEscobar

-- Non-Borelness of the countable well-order class (issue #33; consumes López–Escobar + #12 + #13)
import InfinitaryLogic.Descriptive.WellOrderNonBorel

-- Counting theorems (depend on descriptive results)
import InfinitaryLogic.ModelTheory.CountingCountable
import InfinitaryLogic.ModelTheory.MorleyCounting

/-!
# Descriptive: descriptive set theory of Lω₁ω model classes

Import this bundle for the structure space, satisfaction measurability,
Borel complexity, counting dichotomy, finite carrier analysis, and the
countable-model counting theorems.

It also provides a reusable, model-theory-free DST library (pure Mathlib
imports), developed for the proof of Silver's theorem:

- `CantorAntichain`: Cantor-scheme → perfect-antichain extraction
- `PerfectAntichain`: perfect/Cantor-antichain and thinness vocabulary, plus the perfect-set
  and Polish-quotient cardinal facts
- `StructureIsoSetoid`: the ambient isomorphism relation on `StructureSpace L`, and the
  sentence-level perfect-set/thinness predicates stated against it
- `RankedThinness`: the countable-ordinal rank route to thinness (`ThinRankAnalysis`), with
  the quotient-countability step (`Setoid.countable_antichain`)
  (`CantorScheme.exists_antichain_map` and the splitting-predicate builder);
- `Mycielski`: Mycielski's theorem for Cantor space (`mycielski_cantor`);
- `KuratowskiUlam`: the meager-sections direction of Kuratowski–Ulam
  (`isMeagre_of_isMeagre_sections`);
- `GSGraph`: the graphs `G_S(2^ℕ)` and Miller's independence lemma
  (`exists_gSGraph_edge_of_not_isMeagre`);
- `G0Dichotomy`: the KST independent-superset lemma
  (`exists_measurableSet_relIndependent_superset`) and the positivity
  ideals (`SmallFam`) with the combination lemma (`not_smallFam_comb_cross`);
- `G0Fusion`: the fusion recursion and limit (`G0Fusion.exists_gsGraph_hom`),
  the classical `G₀`-dichotomy construction.

**Note**: the Silver chain (Silver-Burgess, the category route, and
Gandy-Harrington — all sorry-free) lives in `InfinitaryLogic.Conditional`.
`CountingCountable`
and `MorleyCounting` depend on descriptive results and are included here.
-/
