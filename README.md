# Infinitary Logic in Lean 4

A Lean 4 formalization of infinitary logic and Scott sentences, building on Mathlib. This project is under active development.

## Goals

1. **Scott Sentences** - Every countable structure in a relational countable language has a Scott sentence that characterizes it up to isomorphism.

2. **Scott Rank < ω₁** - The Scott rank of any countable structure is a countable ordinal.

3. **Karp's Theorem** - Back-and-forth equivalence at all ordinals characterizes Lω₁ω elementary equivalence.

4. **Model Existence / Completeness** - Consistency properties yield models for Lω₁ω theories.

5. **López-Escobar Theorem** (future) - Borel isomorphism-invariant sets of structures are Lω₁ω-definable.

## Current Status

The project compiles with Mathlib v4.27.0. Core definitions and main theorem statements are complete, with **7 sorry placeholders** remaining across 5 modules (see breakdown below). Most major results are fully proved.

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

**Scott sentences** (sorry-free except for `per_tuple_stabilization_below_omega1`):
- Atomic diagrams for relational languages
- Back-and-forth equivalence (`BFEquiv`) indexed by ordinals
- Scott formula and Scott sentence definitions
- Scott rank definition
- `realize_scottFormula_iff_BFEquiv` (Scott formula captures BF-equivalence)
- `scottSentence_characterizes` — depends on `per_tuple_stabilization_below_omega1`
- `scottRank_lt_omega1` — depends on `per_tuple_stabilization_below_omega1`

**Karp's theorem** (fully proved, sorry-free):
- `karp_theorem_w` (BFEquiv at all ordinals ↔ agree on all `LinfEquivW` sentences)
- `BFEquiv_iff_agree_formulas_omega` (sorry-free)

**Model existence** (fully proved, sorry-free):
- Consistency properties, Henkin construction, truth lemma
- `model_existence` theorem with term model construction
- Omitting types theorem (sorry)

**Model theory:**
- Downward Löwenheim–Skolem for Lω₁ω (sorry-free)
- Hanf number bounds (sorry)
- Counting models results (inherits sorry from `per_tuple_stabilization_below_omega1`)

**Admissible fragments:**
- Barwise compactness (sorry)
- Nadel bound (sorry-free)

### Remaining Sorries (7)

| File | Count |
|------|------:|
| Scott/Sentence.lean | 3 |
| Scott/Rank.lean | 1 |
| ModelExistence/Completeness.lean | 1 |
| Admissible/Compactness.lean | 1 |
| ModelTheory/Hanf.lean | 1 |

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
│   ├── Sentence.lean                    # scottSentence and main theorem
│   ├── Rank.lean                        # elementRank, scottRank, bounds
│   ├── Height.lean                      # Scott height and related bounds
│   └── QuantifierRank.lean              # Quantifier rank lemmas for Scott constructs
├── Karp/                                # Karp's theorem
│   ├── Theorem.lean                     # karp_theorem_w (sorry-free)
│   ├── PotentialIso.lean                # Potential isomorphisms and BFEquiv
│   └── CountableCorollary.lean          # Corollaries for countable structures
├── ModelExistence/                      # Model existence for Lω₁ω
│   ├── ConsistencyProperty.lean         # Consistency property definition
│   ├── Theorem.lean                     # Model existence theorem
│   └── Completeness.lean                # Completeness for Lω₁ω
├── ModelTheory/                         # Classical model-theoretic results
│   ├── LowenheimSkolem.lean             # Downward Löwenheim–Skolem for Lω₁ω
│   ├── Hanf.lean                        # Hanf number bounds
│   └── CountingModels.lean              # Counting models results
└── Admissible/                          # Admissible fragments
    ├── Fragment.lean                     # Admissible fragment definitions
    ├── Compactness.lean                  # Barwise compactness
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

Requires Lean 4 with Mathlib. See `lakefile.toml` for exact versions.

## References

- Barwise, J. (1975). *Admissible Sets and Structures*
- Hodges, W. (1993). *Model Theory*, Chapter 3
- Marker, D. (2002). *Model Theory: An Introduction*, Chapter 2.6

## License

Apache 2.0
