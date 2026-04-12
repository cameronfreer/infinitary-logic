import InfinitaryLogic.All

/-!
# Infinitary Logic

This library formalizes infinitary logic, including:
- L∞ω: Infinitary logic with arbitrary conjunctions/disjunctions
- Lω₁ω: Countable infinitary logic (countable conjunctions/disjunctions)
- Scott sentences and Scott rank for characterizing countable structures

## Main Results

- Every countable structure in a relational countable language has a Scott sentence
  that characterizes it up to isomorphism.
- The Scott rank of a countable structure is a countable ordinal (< ω₁).
- L∞ω is the union of all Lκω for cardinals κ; Lω₁ω = L(ℵ₁)ω.

The unconditional API is recovered via `countableRefinementHypothesis` (proved in
`Scott/RefinementCount.lean`). Conditional `_of` variants taking
`CountableRefinementHypothesis` as a hypothesis are also available.

## Import Bundles

For targeted imports, use one of these entry points instead of importing
this file directly:
- `InfinitaryLogic.Core`: syntax, semantics, Scott analysis, Karp's theorem
- `InfinitaryLogic.Countable`: model existence, Löwenheim-Skolem, Hanf, counting, EM chain
- `InfinitaryLogic.Admissible`: admissible fragments, Barwise compactness, proof system
- `InfinitaryLogic.Descriptive`: descriptive set theory of model classes

## Organization

### L∞ω (Linf/)
- `Linf/Syntax.lean`: Syntax of L∞ω formulas with arbitrary index types
- `Linf/Semantics.lean`: Semantics (Realize)
- `Linf/Operations.lean`: Operations (relabel, castLE, subst, FO embedding)
- `Linf/Countability.lean`: IsCountable and IsKappa predicates

### Lω₁ω (Lomega1omega/)
- `Lomega1omega/Syntax.lean`: Syntax of Lω₁ω formulas with ℕ-indexed connectives
- `Lomega1omega/Semantics.lean`: Semantics (Realize)
- `Lomega1omega/Operations.lean`: Operations (relabel, castLE, subst)
- `Lomega1omega/Embedding.lean`: Embeddings between Lω₁ω and L∞ω

### Scott sentences (Scott/)
- `Scott/AtomicDiagram.lean`: Atomic types for relational languages
- `Scott/BackAndForth.lean`: Back-and-forth equivalence
- `Scott/Formula.lean`: Scott formula construction
- `Scott/Code.lean`: Countable formula codes (FormulaCode, encoding, BFEquiv bridge)
- `Scott/Sentence.lean`: Scott sentence and characterization theorem (`_of` variants)
- `Scott/RefinementCount.lean`: CRH theorem + unconditional Sentence-level wrappers
- `Scott/Rank.lean`: Scott rank definition and bounds
- `Scott/QuantifierRank.lean`: Quantifier rank bounds on Scott formulas
- `Scott/Height.lean`: Scott height, canonical Scott sentence, sr/SR

### Karp's theorem (Karp/)
- `Karp/PotentialIso.lean`: Potential isomorphism definition
- `Karp/Theorem.lean`: Karp's theorem (potential iso ↔ L∞ω-equivalence)
- `Karp/CountableCorollary.lean`: Countable structures corollary

### Model existence (ModelExistence/)
- `ModelExistence/ConsistencyProperty.lean`: Consistency property axioms (C0)-(C7)
- `ModelExistence/HenkinConstruction.lean`: Henkin construction infrastructure (maximal consistent sets)
- `ModelExistence/Theorem.lean`: Model existence theorem
- `ModelExistence/Completeness.lean`: Karp completeness and omitting types

### Model theory (ModelTheory/)
- `ModelTheory/LowenheimSkolem.lean`: Downward Löwenheim-Skolem for Lω₁ω
- `ModelTheory/Hanf.lean`: Hanf numbers and Morley-Hanf bound
- `ModelTheory/EM/Indiscernible.lean`: Lω₁ω-indiscernible sequences API (restrict, reindex, pair/unary invariance)
- `ModelTheory/EM/Template.lean`: Ehrenfeucht–Mostowski templates — bridge between indiscernible sequences and EM stretching
- `ModelTheory/EM/Realization.lean`: template → L[[J]]-theory bridge; finite satisfiability of `templateTheory h.template J` in the source indiscernible
- `ModelTheory/CountingModels.lean`: Scott rank and model counting
- `ModelTheory/CountingCountable.lean`: Counting theorem for all countable models
- `ModelTheory/MorleyCounting.lean`: Morley's counting theorem (≤ ℵ₁ or 2^ℵ₀)

### Admissible sets (Admissible/)
- `Admissible/Fragment.lean`: `AdmissibleFragmentCore` (closure properties) + `AdmissibleFragment` (core + finite-subset compactness)
- `Admissible/Barwise/Data.lean`: `BarwiseCompactnessData` — literature-faithful Barwise compactness interface with A-coded subtheories
- `Admissible/Barwise/ProofSystem.lean`: Derivability in admissible-fragment proof system
- `Admissible/Barwise/Soundness.lean`: Soundness of the proof system
- `Admissible/Barwise/ConsistencyBridge.lean`: Bridge from AConsistent to ConsistencyPropertyEq
- `Admissible/WithConstants.lean`: `admissibleFragmentOfUniv` — admissible fragment from a bare compactness hypothesis
- `Admissible/Compactness.lean`: Barwise compactness and completeness
- `Admissible/Nadel.lean`: Nadel bound on Scott height

### Descriptive set theory (Descriptive/)
- `Descriptive/StructureSpace.lean`: Coding space for countable structures on ℕ
- `Descriptive/Measurable.lean`: Measurable space structure on the coding space
- `Descriptive/Topology.lean`: Topological structure on the coding space
- `Descriptive/Polish.lean`: Polish space and standard Borel space instances
- `Descriptive/SatisfactionBorel.lean`: Borel complexity of Lω₁ω satisfaction
- `Descriptive/BFEquivBorel.lean`: Borel complexity of BF-equivalence
- `Descriptive/IsomorphismBorel.lean`: Isomorphism is Borel under bounded Scott height
- `Descriptive/ModelClassStandardBorel.lean`: Model classes are standard Borel
- `Descriptive/CountingDichotomy.lean`: Conditional counting dichotomy (Silver–Burgess)
- `Descriptive/SatisfactionBorelOn.lean`: Generic satisfaction measurability for carrier-parametric spaces
- `Descriptive/FiniteCarrier.lean`: Finite-carrier counting via permutation orbits; combined dichotomy
- `Descriptive/SilverBurgess.lean`: Silver-Burgess dichotomy (1 sorry: Borel→closed reduction)
-/
