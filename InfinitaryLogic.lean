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

`import InfinitaryLogic` loads the sorry-free surface (`InfinitaryLogic.All`).
For narrower entry points:
- `InfinitaryLogic.Core`: syntax, semantics, Scott analysis, Karp's theorem
- `InfinitaryLogic.Countable`: model existence, Löwenheim-Skolem, Hanf, counting, EM chain
- `InfinitaryLogic.Admissible`: admissible fragments, Barwise compactness, proof system
- `InfinitaryLogic.Descriptive`: descriptive set theory of model classes
- `InfinitaryLogic.Conditional`: the Silver chain and the Morley–Hanf chain (both proved;
  the directory name is historical)
- `InfinitaryLogic.Everything`: everything including `Conditional/` and the
  legacy off-path modules (not sorry-free)

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
- `Scott/Code.lean`: LEGACY/off-path countable formula codes (`FormulaCode`; the Scott pipeline
  is decoupled from this bridge — kept for its public API, reachable via `Everything` only)
- `Scott/Sentence.lean`: Scott sentence and characterization theorem (`_of` variants)
- `Scott/RefinementCount.lean`: CRH theorem + unconditional Sentence-level wrappers
- `Scott/Rank.lean`: Scott rank definition and bounds
- `Scott/QuantifierRank.lean`: Quantifier rank bounds on Scott formulas
- `Scott/Height.lean`: Scott height, canonical Scott sentence, sr/SR

### Karp's theorem (Karp/)
- `Karp/PotentialIso.lean`: Potential isomorphism definition
- `Karp/Theorem.lean`: Karp's theorem (potential iso ↔ L∞ω-equivalence)
- `Karp/CountableCorollary.lean`: Countable structures corollary

### Methods (Methods/)
- `Methods/Henkin/ConsistencyProperty.lean`: Consistency property axioms (C0)-(C7)
- `Methods/Henkin/Construction.lean`: Henkin construction infrastructure (maximal consistent sets)
- `Methods/Henkin/ModelExistence.lean`: Model existence theorem
- `Methods/Henkin/Completeness.lean`: Karp completeness and omitting types
- `Methods/Henkin/SatisfiableConsistencyProperty.lean`: ConsistencyPropertyEq from model + naming function
- `Methods/EM/Indiscernible.lean`: Lω₁ω-indiscernible sequences API (restrict, reindex, pair/unary invariance)
- `Methods/EM/Template.lean`: Ehrenfeucht–Mostowski templates — bridge between indiscernible sequences and EM stretching
- `Methods/EM/Realization.lean`: template → L[[J]]-theory bridge; finite satisfiability of `templateTheory h.template J` in the source indiscernible
- `Methods/EM/Extraction.lean`: extraction of indiscernible sequences (Ramsey side of the EM chain)
- `Methods/EM/FragmentAdapter.lean`: admissible-fragment adapter theorems (`_of_fragment`, `_of_fullFragment`, `_of_compact`; imported by the `Admissible` bundle)
- `Methods/TailIndiscernible.lean`: neutral bare definition of `IsLomega1omegaIndiscernibleOnTail` (EM-free, shared by `TailAdapter` and the local `EMContext` re-base)
- `Methods/EM/TailAdapter.lean`: tail-indiscernibility variants (tail templates, finite satisfiability, stretching) built on the neutral `IsLomega1omegaIndiscernibleOnTail`
- WIP frontier (non-default `InfinitaryLogicWIP` target, excluded from `All`/`Everything`):
  `Methods/Skolem.lean`, `Methods/SkolemColimit.lean`, `Methods/SkolemClosure.lean` (the
  `skolemStage`/`skolemColim` tower and the countable staged family `Γ*`),
  `Methods/EMTermModel.lean` (EM term model, staged truth lemma `truthLemmaStage`),
  `Methods/LocalEMSupport.lean`, `Methods/LocalSkolem.lean`, `Methods/LocalTower.lean`,
  `Methods/LocalColimit.lean`, `Methods/LocalEMFamily.lean`, `Methods/LocalEMExtraction.lean`,
  `Methods/LocalEMContext.lean`, `Methods/LocalEMTruth.lean` (countable family-restricted re-base:
  shared generic support, `localSkolem`, the `Llocal`/`Γlocal` tower with `skolemNeed`, the
  countable colimit `localColim` with cocone and `ΓlocalColim`, the countable atom/deForm family
  `ΓEMlocal`, the tail-extraction bridge, the generic deep-interpretation semantic layer, the
  `LocalEMEq` quotient carrier + `Λ[[J]]`-`Structure` (`LocalEMContext`), the concrete
  instantiation `exists_localEMContext`, and the local Skolem-witness transport `LocalEMTruth`)

### Model theory (ModelTheory/)
- `ModelTheory/LowenheimSkolem.lean`: Downward Löwenheim-Skolem for Lω₁ω
- `ModelTheory/Hanf.lean`: Hanf numbers; the Morley-Hanf bound itself is `morley_hanf` in `Conditional/MorleyHanfSchemaDischarge.lean`
- `ModelTheory/HanfSpectrum.lean` (+ `HanfSpectrum/`): the sharpness half — bounded-spectrum witnesses (countable spectrum, powerset, the Exercise 5.3 beth ladder over the von Neumann hierarchy) and the exact Hanf number `Lomega1omegaHanfNumber_eq_beth_omega1`
- `ModelTheory/CountingModels.lean`: Scott rank and model counting
- `ModelTheory/CountingCountable.lean`: Counting theorem for all countable models
- `ModelTheory/MorleyCounting.lean`: Morley's counting theorem (≤ ℵ₁ or 2^ℵ₀)

### Admissible sets (Admissible/)
- `Admissible/Fragment.lean`: `AdmissibleFragmentCore` (closure properties) + `FiniteCompactFragment` (core + finite-subset compactness)
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
- `Descriptive/CantorAntichain.lean`: Cantor-scheme antichain extraction (completeness-free core)
- `Descriptive/Mycielski.lean`: Mycielski's theorem
- `Descriptive/KuratowskiUlam.lean`: Kuratowski–Ulam
- `Descriptive/GSGraph.lean`: the `G_S` graphs
- `Descriptive/G0Dichotomy.lean`: the classical G₀ dichotomy
- `Descriptive/G0Fusion.lean`: G₀ fusion machinery

### Combinatorics (Combinatorics/)
- `Combinatorics/InfiniteRamsey.lean`: n-ary infinite Ramsey on ℕ (`infinite_ramsey_nat_arity`)
- `Combinatorics/InfiniteRamseyFamily.lean`: family/diagonal version (`infinite_ramsey_nat_family`) — a finished reusable result; no longer on the `morley_hanf` route (injective sequences are already seed-indiscernible)
- `Combinatorics/PairErdosRadoGeneral.lean`, `Combinatorics/EndHomogeneousErdosRado.lean`, `Combinatorics/FiniteArityErdosRadoInduction.lean`: the bounded finite-arity Erdős–Rado chain (`finiteArityHomogeneousUpTo_beth_stage`) — the combinatorial engine of `morley_hanf`'s Marker certification (on the `InfinitaryLogicWIP` target and the endpoint's dependency cone)
- the exploratory all-arities ladder `Combinatorics/ErdosRado.lean` (false target in ZFC) is preserved on the `archive/legacy-erdos-rado` branch, not in the tree

### Conditional (Conditional/)
- `Conditional/MorleyHanfTransfer.lean`: the Morley–Hanf reduction chain (historical conditional forms; extraction side discharged by `morleyHanfExtractionTail_holds`)
- `Conditional/MorleyHanfSchemaDischarge.lean`: `MorleySeedTailTemplateRealizable` proved via the schema completion; the unconditional endpoint `morley_hanf`
- `Conditional/SilverBurgess.lean`: Silver–Burgess dichotomy (sorry-free)
- `Conditional/GandyHarrington.lean`: Silver-for-Borel via Gandy–Harrington-style core (`gandy_harrington_for_relation`, sorry-free, axiom-clean)
- `Conditional/SilverCategoryRoute.lean`: Silver's theorem via Miller's classical category route (Mycielski + KU + G₀ fusion)
-/
