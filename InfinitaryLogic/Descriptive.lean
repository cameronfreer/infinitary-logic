-- Structure space and measurability
import InfinitaryLogic.Descriptive.StructureSpace
import InfinitaryLogic.Descriptive.Measurable
import InfinitaryLogic.Descriptive.Topology
import InfinitaryLogic.Descriptive.Polish
import InfinitaryLogic.Descriptive.GDeltaPolish
import InfinitaryLogic.Descriptive.ModelsOfGDelta
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
import InfinitaryLogic.Descriptive.BorelFunctionalGraph
import InfinitaryLogic.Descriptive.CantorAntichain
import InfinitaryLogic.Descriptive.PerfectAntichain
import InfinitaryLogic.Descriptive.StructureIsoSetoid
import InfinitaryLogic.Descriptive.RankedThinness
import InfinitaryLogic.Descriptive.Mycielski
import InfinitaryLogic.Descriptive.KuratowskiUlam
import InfinitaryLogic.Descriptive.GSGraph
import InfinitaryLogic.Descriptive.G0Dichotomy
import InfinitaryLogic.Descriptive.G0Fusion
import InfinitaryLogic.Descriptive.CantorStabilization
import InfinitaryLogic.Descriptive.KleeneBrouwer
import InfinitaryLogic.Descriptive.TreeCodes

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
import InfinitaryLogic.Descriptive.WellOrderBridge

-- THE LÓPEZ–ESCOBAR THEOREM: both packaged equivalences and the collection equality (issue #10)
import InfinitaryLogic.Descriptive.LopezEscobar

-- Non-Borelness of the countable well-order class (issue #33; consumes López–Escobar + #12 + #13)
import InfinitaryLogic.Descriptive.WellOrderNonBorel

-- Boundedness for analytic families of coded well-orders (issue #64; the PC sandwich + #12 + #13)
import InfinitaryLogic.Descriptive.AnalyticWellOrderBoundedness
import InfinitaryLogic.Descriptive.WellOrderRankedThinness
import InfinitaryLogic.Descriptive.WellOrderThin
import InfinitaryLogic.Descriptive.InvariantSeparation
import InfinitaryLogic.Descriptive.SentenceRecovery
import InfinitaryLogic.Descriptive.CountableSplits
import InfinitaryLogic.Descriptive.SentenceSplits
import InfinitaryLogic.Descriptive.SmallVocabulary
import InfinitaryLogic.Descriptive.SmallVocabularyLift
import InfinitaryLogic.Descriptive.SmallVocabularyTransport
import InfinitaryLogic.Descriptive.ObservableConstancy
import InfinitaryLogic.Descriptive.ScottDefinability
import InfinitaryLogic.Descriptive.PerfectSetDichotomy
import InfinitaryLogic.OrdinalCountability
import InfinitaryLogic.Descriptive.SentenceObservables
import InfinitaryLogic.Descriptive.FragmentTail
import InfinitaryLogic.Descriptive.FragmentSpectrum
import InfinitaryLogic.Descriptive.MorleyizationCode
import InfinitaryLogic.Descriptive.RealizedSpectrum
import InfinitaryLogic.Descriptive.AntichainTransport
import InfinitaryLogic.Descriptive.MorleyizationThin

-- Counting theorems (depend on descriptive results)
import InfinitaryLogic.ModelTheory.CountingCountable
import InfinitaryLogic.ModelTheory.MorleyCounting
import InfinitaryLogic.ModelTheory.BFExtensionSpectrum
import InfinitaryLogic.ModelTheory.BFLimitIsolation
import InfinitaryLogic.ModelTheory.BFSmallCounting

/-!
# Descriptive: descriptive set theory of Lω₁ω model classes

Import this bundle for the structure space, satisfaction measurability,
Borel complexity, counting dichotomy, finite carrier analysis, and the
countable-model counting theorems.

It also provides reusable DST infrastructure, developed for the proof of
Silver's theorem.  Everything below is generic — pure Mathlib imports, no model
theory — except `StructureIsoSetoid`, which is deliberately the model-theoretic
application of that vocabulary:

- `OrdinalCountability` (top level, no logic): countability of a set equals boundedness of a
  countable-fibre rank below `ω₁`, countable complements from countable successor losses under
  an explicit limit hypothesis, exhaustion by antitone domains giving cardinality exactly `ℵ₁`,
  and uncountability of Cantor space by cardinal arithmetic
- `GDeltaPolish` (Mathlib only): a Gδ subset of a Polish space is Polish, and standard Borel, in
  its subspace topology (`IsGδ.polishSpace`, `IsGδ.standardBorelSpace`); `ModelsOfGDelta`: a Gδ
  set of coded models is Polish in the inherited topology (`polishSpace_modelsOf_of_isGδ`,
  conditional on the Gδ hypothesis, which is not automatic), with closure of the Gδ property
  under finite, countable, and encodable conjunctions
- `CantorAntichain`: Cantor-scheme → perfect-antichain extraction
  (`CantorScheme.exists_antichain_map` and the splitting-predicate builder);
- `PerfectAntichain`: perfect/Cantor-antichain and thinness vocabulary, plus the perfect-set
  and Polish-quotient cardinal facts
- `StructureIsoSetoid`: **the application** — isomorphism defined once on the ambient
  `StructureSpace L`, `isoSetoid φ` as its restriction, and the sentence-level
  perfect-set/thinness predicates stated against it
- `CountableSplits`: countably many predicates with countable truth sides are simultaneously
  constant off one countable set, and any function of their truth values has countable range
  (`countable_range_of_splits`); consumed by `SentenceSplits`, the thinness criterion from
  single-sentence splits on a presentation of the isomorphism classes
  (`isThinOn_of_countable_sentence_splits`)
- `SmallVocabulary`, `SmallVocabularyLift`: a chosen `Language.{0, 0}` presentation of a countable
  relational `L : Language.{u, v}` (relation symbols shrunk, the decoding `LHom`), the code
  homeomorphism with isomorphism preserved and reflected (`iso_code_iff`), and the formula lift
  preserving realization and quantifier rank (`realize_liftFormula`, `qrank_liftFormula`);
  `SmallVocabularyTransport`: the `Language.{0, 0}` descriptive theorems (López–Escobar, the
  relative pullbacks, Cantor and observable recovery, the spectrum and splits thinness endpoints)
  transported to every countable relational `L : Language.{u, v}` through that presentation;
  `ObservableConstancy`: Borel observations on a presentation of the classes are constant off
  countably many presentation values (`constant_off_countable_of_borel_observation`), with
  measurability on the composite only
- `ScottDefinability`: Scott isolation of a surjective, satisfaction-compatible,
  isomorphism-preserving presentation (`isolatedPresentation_of_surjective`); under the
  single-sentence-split hypothesis, the sentence-definable sets of presentation values are exactly
  the countable and the cocountable ones (`sentence_definable_iff_of_presentation`)
- `PerfectSetDichotomy`: the `ℕ`-tier and all-countable perfect-set dichotomies and their
  refutations from `ℕ`-tier thinness with uncountably many `ℕ`-isomorphism classes and explicit
  finite-tier premises (`Sentenceω.not_perfectSetDichotomyAllCountable_of_thin`)
- `RankedThinness`: the countable-ordinal rank route to thinness (`ThinRankAnalysis`), with
  the quotient-countability step (`Setoid.countable_antichain`);
- `BorelFunctionalGraph`: Borel graphs with singleton vertical sections — Borel domain,
  measurable-embedding projection, and the induced measurable partial function, all via
  Lusin–Souslin;
- `Mycielski`: Mycielski's theorem for Cantor space (`mycielski_cantor`);
- `CantorStabilization`: countably many Borel-fibred maps on Cantor space are simultaneously
  continuous along one continuous injective Cantor subcopy
  (`CantorStabilization.exists_subcopy_continuous`), with the Borel-set form of the Cantor-copy
  extraction (`MeasurableSet.exists_nat_bool_injection_of_not_countable`);
- `KleeneBrouwer`: the Kleene–Brouwer order on a tree over `ℕ` — no infinite branch is
  well-foundedness of strict extension, KB is a well-order on a well-founded tree
  (`KleeneBrouwer.isWellOrder_kbLT`), and the tree height is bounded by the KB order type
  (`KleeneBrouwer.treeHeight_le_type`);
- `TreeCodes`: tree codes over a countable alphabet, the closed tree class, the continuous
  Kleene–Brouwer code into `Language.order`, and analytic boundedness for well-founded trees
  (`analytic_wellFoundedTree_rank_boundedness`) with its domination adapter;
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
The model-theoretic counting modules imported above depend on descriptive results and are
included here.
-/
