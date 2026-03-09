# Infinitary Logic in Lean 4

A Lean 4 formalization of infinitary logic and Scott sentences, building on Mathlib. This project is under active development.

## Goals

1. **Scott Sentences** - Every countable structure in a relational countable language has a Scott sentence that characterizes it up to isomorphism.

2. **Scott Rank < ω₁** - The Scott rank of any countable structure is a countable ordinal.

3. **Karp's Theorem** - Back-and-forth equivalence at all ordinals characterizes infinitary elementary equivalence.

4. **Model Existence / Completeness** - Consistency properties yield models for Lω₁ω theories.

5. **López-Escobar Theorem** (future) - Borel isomorphism-invariant sets of structures are Lω₁ω-definable.

## Current Status

The project targets Lean 4 / Mathlib `v4.27.0`. There are currently **no `sorry` placeholders**
in `InfinitaryLogic/*.lean`.

The main remaining boundaries are mathematical scope rather than proof holes:

- some results are formalized **conditionally** on explicit hypotheses such as
  `CountableRefinementHypothesis` or `MorleyHanfTransfer`
- some high-level theorems are present only in **schematic** form, where the intended
  statement is explained in the docstring but the Lean theorem is intentionally weaker
  pending more infrastructure

## Blueprint

The interactive blueprint with dependency graph is deployed at:

- **[Live Blueprint](https://cameronfreer.github.io/infinitary-logic/blueprint/)**
  (web, with dependency graph)
- **[Blueprint PDF](https://cameronfreer.github.io/infinitary-logic/blueprint.pdf)**

To regenerate locally:

```bash
lake build :blueprint
leanblueprint web   # → blueprint/web/
leanblueprint pdf   # → blueprint/print/print.pdf
```

### Implemented Results

**L∞ω (arbitrary infinitary logic):**
- L∞ω syntax (`BoundedFormulaInf` with arbitrary index types for iSup/iInf)
- L∞ω semantics (`Realize` with simp lemmas for all connectives)
- `IsCountable` predicate characterizing membership in Lω₁ω
- `IsKappa` predicate characterizing membership in Lκω
- `isCountable_iff_isKappa_aleph1` (IsCountable ↔ IsKappa ℵ₁)
- `indexBound` computing maximum index type cardinality
- `exists_isKappa` (union view: every L∞ω formula belongs to some Lκω)

**Lω₁ω (countable infinitary logic):**
- Lω₁ω syntax (`BoundedFormulaω` with ℕ-indexed conjunctions/disjunctions)
- Lω₁ω semantics (`Realize` with simp lemmas for all connectives)
- Embedding of first-order logic into Lω₁ω (`BoundedFormula.toLω`)
- Embedding of Lω₁ω into L∞ω (`BoundedFormulaω.toLinf`)
- Conversion from countable L∞ω to Lω₁ω (`BoundedFormulaInf.ofCountable`)
- Quantifier rank definitions and monotonicity lemmas

**Scott sentences and Scott analysis** (proved):
- Atomic diagrams for relational languages
- Back-and-forth equivalence (`BFEquiv`) indexed by ordinals
- Scott formula and Scott sentence definitions
- Scott height and Scott rank definitions
- `countableRefinementHypothesis` (countability of refinement ordinals)
- `realize_scottFormula_iff_BFEquiv` (Scott formula captures BF-equivalence)
- `scottSentence_characterizes`
- `scottRank_lt_omega1`
- `scottHeight_lt_omega1`

**Karp's theorem** (fully proved, sorry-free):
- `karp_theorem_w` (potential isomorphism ↔ `LinfEquivW`)
- countable corollaries: `LomegaEquiv` / `LinfEquiv` imply isomorphism for countable structures

**Model existence** (fully proved, sorry-free):
- Consistency properties, Henkin construction, truth lemma
- `model_existence` theorem with term model construction
- `karp_completeness`
- `omitting_types`

**Model theory:**
- Downward Löwenheim–Skolem for Lω₁ω (sorry-free)
- Hanf number existence (`hanf_existence`)
- conditional Morley-Hanf bound (`morley_hanf_of_transfer`)
- Scott-height-based counting-models infrastructure
- schematic Morley counting dichotomy

**Admissible fragments:**
- Barwise compactness
- Barwise completeness II
- Nadel bound (sorry-free)

### Current Boundaries

- `CountableRefinementHypothesis` is now proved internally, but it remains a genuine
  mathematical boundary in the Scott-analysis architecture and is highlighted as such in the code.
- `morley_hanf_of_transfer` is conditional on the explicit hypothesis
  `MorleyHanfTransfer`, which packages deep Erdős-Rado / Ehrenfeucht-Mostowski machinery.
- `morley_counting_dichotomy` is currently schematic (`True` in Lean) pending descriptive
  set theory infrastructure for coding countable structures and applying Silver-Burgess style results.

## File Structure

```
InfinitaryLogic.lean                     # Top-level entrypoint (imports Basic)
InfinitaryLogic/
├── Basic.lean                           # Re-exports all modules
├── Linf/                                # L∞ω infrastructure
│   ├── Syntax.lean                      # BoundedFormulaInf with arbitrary index types
│   ├── Semantics.lean                   # Realize function and simp lemmas
│   ├── Operations.lean                  # relabel, castLE, subst, FO embedding
│   ├── Countability.lean                # IsCountable, IsKappa predicates
│   ├── Theory.lean                      # L∞ω theories
│   └── QuantifierRank.lean              # Quantifier rank for L∞ω
├── Lomega1omega/                        # Lω₁ω infrastructure
│   ├── Syntax.lean                      # BoundedFormulaω with ℕ-indexed connectives
│   ├── Semantics.lean                   # Realize function and simp lemmas
│   ├── Operations.lean                  # relabel, castLE, subst, FO embedding
│   ├── Embedding.lean                   # toLinf, ofCountable conversions
│   ├── Theory.lean                      # Lω₁ω theories
│   └── QuantifierRank.lean              # Quantifier rank for Lω₁ω
├── Scott/                               # Scott sentences and rank
│   ├── AtomicDiagram.lean               # AtomicIdx, atomicFormula, SameAtomicType
│   ├── BackAndForth.lean                # BFEquiv, BFStrategy, BFStrategyOmega
│   ├── Formula.lean                     # scottFormula construction
│   ├── Sentence.lean                    # stabilization, conditional Scott pipeline
│   ├── RefinementCount.lean             # CRH proof and unconditional Scott wrappers
│   ├── Rank.lean                        # elementRank, scottRank, bounds
│   ├── Height.lean                      # Scott height and canonical Scott sentence
│   └── QuantifierRank.lean              # Quantifier rank lemmas for Scott constructs
├── Karp/                                # Karp's theorem
│   ├── Theorem.lean                     # karp_theorem_w and related equivalence results
│   ├── PotentialIso.lean                # Potential isomorphisms and BFEquiv
│   └── CountableCorollary.lean          # Corollaries for countable structures
├── ModelExistence/                      # Model existence for Lω₁ω
│   ├── ConsistencyProperty.lean         # Consistency property definition
│   ├── Theorem.lean                     # Model existence theorem
│   ├── SatisfiableConsistencyProperty.lean # Model-theoretic consistency properties
│   └── Completeness.lean                # Karp completeness and omitting types
├── ModelTheory/                         # Classical model-theoretic results
│   ├── LowenheimSkolem.lean             # Downward Löwenheim–Skolem for Lω₁ω
│   ├── Hanf.lean                        # Hanf numbers and conditional Morley-Hanf bound
│   └── CountingModels.lean              # Scott-height bounds and counting-models skeleton
└── Admissible/                          # Admissible fragments
    ├── Fragment.lean                     # Admissible fragment definitions
    ├── Compactness.lean                  # Barwise compactness and completeness II
    └── NadelBound.lean                   # Nadel bound
```

## Key Definitions

### L∞ω Formulas

```lean
-- Index types live in universe uι (parameterized)
inductive BoundedFormulaInf (L : Language) (α : Type u') : ℕ → Type (max u v u' (uι + 1))
  | falsum : BoundedFormulaInf α n
  | equal : L.Term (α ⊕ Fin n) → L.Term (α ⊕ Fin n) → BoundedFormulaInf α n
  | rel : L.Relations l → (Fin l → L.Term (α ⊕ Fin n)) → BoundedFormulaInf α n
  | imp : BoundedFormulaInf α n → BoundedFormulaInf α n → BoundedFormulaInf α n
  | all : BoundedFormulaInf α (n + 1) → BoundedFormulaInf α n
  | iSup {ι : Type uι} : (ι → BoundedFormulaInf α n) → BoundedFormulaInf α n  -- arbitrary disjunction
  | iInf {ι : Type uι} : (ι → BoundedFormulaInf α n) → BoundedFormulaInf α n  -- arbitrary conjunction
```

### Lω₁ω Formulas

```lean
inductive BoundedFormulaω (L : Language) (α : Type*) : ℕ → Type _
  | falsum : BoundedFormulaω α n
  | equal : L.Term (α ⊕ Fin n) → L.Term (α ⊕ Fin n) → BoundedFormulaω α n
  | rel : L.Relations l → (Fin l → L.Term (α ⊕ Fin n)) → BoundedFormulaω α n
  | imp : BoundedFormulaω α n → BoundedFormulaω α n → BoundedFormulaω α n
  | all : BoundedFormulaω α (n + 1) → BoundedFormulaω α n
  | iSup : (ℕ → BoundedFormulaω α n) → BoundedFormulaω α n  -- countable disjunction
  | iInf : (ℕ → BoundedFormulaω α n) → BoundedFormulaω α n  -- countable conjunction
```

### Back-and-Forth Equivalence

```lean
def BFEquiv (α : Ordinal) (n : ℕ) (a : Fin n → M) (b : Fin n → N) : Prop
```

BF-equivalence at ordinal α between tuples:
- At 0: same atomic type
- At α + 1: BF-equivalence at α, plus forth and back conditions
- At limit λ: BF-equivalence at all β < λ

### Scott Sentence

```lean
def scottSentence (M : Type*) [L.Structure M] [Countable M] : L.Formulaω (Fin 0)
```

The Scott sentence of M characterizes M up to isomorphism among countable structures.

## Assumptions

**Core syntax/semantics** (Linf, Lomega1omega): General first-order languages, no restrictions.

**Scott/Karp results:**
- Relational languages (`[L.IsRelational]`) — no function symbols
- Countable relation symbols (`[Countable (Σ l, L.Relations l)]`)
- Countable structures (`[Countable M]`)

**Model existence/completeness:** Additionally assumes countable function symbols (`[Countable (Σ l, L.Functions l)]`).

## Building

```bash
lake build
```

See `lakefile.toml` for pinned dependencies and `docs/leanarchitect-blueprint.md`
for the blueprint workflow.

## References

- Barwise, J. (1975). *Admissible Sets and Structures*
- Hodges, W. (1993). *Model Theory*, Chapter 3
- Marker, D. (2002). *Model Theory: An Introduction*, Chapter 2.6

## License

Apache 2.0
