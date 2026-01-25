/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import CountableInfinitaryLogic.Lomega1omega.Syntax
import CountableInfinitaryLogic.Lomega1omega.Semantics
import CountableInfinitaryLogic.Lomega1omega.Operations
import CountableInfinitaryLogic.Scott.AtomicDiagram
import CountableInfinitaryLogic.Scott.BackAndForth
import CountableInfinitaryLogic.Scott.Formula
import CountableInfinitaryLogic.Scott.Sentence
import CountableInfinitaryLogic.Scott.Rank

/-!
# Countable Infinitary Logic

This library formalizes the countable infinitary logic Lω₁ω and Scott sentences.

## Main Results

- Every countable structure in a relational countable language has a Scott sentence
  that characterizes it up to isomorphism.
- The Scott rank of a countable structure is a countable ordinal (< ω₁).

## Organization

- `Lomega1omega/Syntax.lean`: Syntax of Lω₁ω formulas
- `Lomega1omega/Semantics.lean`: Semantics (Realize)
- `Lomega1omega/Operations.lean`: Operations (relabel, castLE, subst)
- `Scott/AtomicDiagram.lean`: Atomic types for relational languages
- `Scott/BackAndForth.lean`: Back-and-forth equivalence
- `Scott/Formula.lean`: Scott formula construction
- `Scott/Sentence.lean`: Scott sentence and characterization theorem
- `Scott/Rank.lean`: Scott rank definition and bounds
-/
