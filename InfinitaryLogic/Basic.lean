/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
-- L∞ω (arbitrary infinitary logic)
import InfinitaryLogic.Linf.Syntax
import InfinitaryLogic.Linf.Semantics
import InfinitaryLogic.Linf.Operations
import InfinitaryLogic.Linf.Countability
import InfinitaryLogic.Linf.Theory
import InfinitaryLogic.Linf.QuantifierRank

-- Lω₁ω (countable infinitary logic)
import InfinitaryLogic.Lomega1omega.Syntax
import InfinitaryLogic.Lomega1omega.Semantics
import InfinitaryLogic.Lomega1omega.Operations
import InfinitaryLogic.Lomega1omega.Embedding
import InfinitaryLogic.Lomega1omega.Theory
import InfinitaryLogic.Lomega1omega.QuantifierRank

-- Scott sentences and ranks
import InfinitaryLogic.Scott.AtomicDiagram
import InfinitaryLogic.Scott.BackAndForth
import InfinitaryLogic.Scott.Formula
import InfinitaryLogic.Scott.Sentence
import InfinitaryLogic.Scott.Rank
import InfinitaryLogic.Scott.QuantifierRank
import InfinitaryLogic.Scott.Height

-- Karp's theorem
import InfinitaryLogic.Karp.PotentialIso
import InfinitaryLogic.Karp.Theorem
import InfinitaryLogic.Karp.CountableCorollary

-- Model existence
import InfinitaryLogic.ModelExistence.ConsistencyProperty
import InfinitaryLogic.ModelExistence.HenkinConstruction
import InfinitaryLogic.ModelExistence.Theorem
import InfinitaryLogic.ModelExistence.Completeness

-- Model theory
import InfinitaryLogic.ModelTheory.LowenheimSkolem
import InfinitaryLogic.ModelTheory.Hanf
import InfinitaryLogic.ModelTheory.CountingModels

-- Admissible sets and Barwise
import InfinitaryLogic.Admissible.Fragment
import InfinitaryLogic.Admissible.Compactness
import InfinitaryLogic.Admissible.NadelBound

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
- `Scott/Sentence.lean`: Scott sentence and characterization theorem
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
- `ModelTheory/CountingModels.lean`: Scott rank and model counting

### Admissible sets (Admissible/)
- `Admissible/Fragment.lean`: Abstract admissible fragments
- `Admissible/Compactness.lean`: Barwise compactness and completeness
- `Admissible/NadelBound.lean`: Nadel bound on Scott height
-/
