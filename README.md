# Countable Infinitary Logic (Lω₁ω) in Lean 4

A Lean 4 formalization of countable infinitary logic Lω₁ω and Scott sentences, building on Mathlib.

## Goals

1. **Scott Sentences** - Every countable structure in a relational countable language has a Scott sentence that characterizes it up to isomorphism.

2. **Scott Rank < ω₁** - The Scott rank of any countable structure is a countable ordinal.

3. **López-Escobar Theorem** (future) - Borel isomorphism-invariant sets of structures are Lω₁ω-definable.

## Current Status

The project compiles successfully with Mathlib v4.27.0. Core definitions and main theorem statements are complete; proofs have documented sorries for chain construction lemmas.

### Completed

- Lω₁ω syntax (`BoundedFormulaω` with countable conjunctions/disjunctions)
- Lω₁ω semantics (`Realize` with simp lemmas for all connectives)
- Embedding of first-order logic into Lω₁ω
- Atomic diagrams for relational languages
- Back-and-forth equivalence (`BFEquiv`) indexed by ordinals
- Scott formula and Scott sentence definitions
- Scott rank definition
- `realize_scottFormula_iff_BFEquiv` (Scott formula captures BF-equivalence)
- `scottSentence_characterizes` (main characterization theorem)
- `scottRank_lt_omega1` (countable bound on Scott rank)

### Remaining Sorries (6)

The main theorems above are proven modulo 6 helper lemmas requiring back-and-forth chain constructions:

**Sentence.lean:**
1. `BFEquiv_omega_implies_IsExtensionPair` (line 248) - Extension property from BFEquiv ω
2. `BFEquiv_omega_implies_equiv` (line 289) - Back-and-forth chain construction
3. `BFEquiv_ge_omega_singleton_implies_equiv_with_image` (line 523) - Chain preserving initial pair

**Rank.lean:**
4. `stabilizationOrdinal_mem_elementRank_set` (line 70) - Language expansion argument
5. `stabilizationOrdinal_le_scottRank` (line 227) - Stabilization bound
6. `scottSentence_eq_scottFormula_rank` (line 260) - Semantic equivalence

## File Structure

```
CountableInfinitaryLogic/
├── Basic.lean                    # Re-exports all modules
├── Lomega1omega/
│   ├── Syntax.lean               # BoundedFormulaω inductive type
│   ├── Semantics.lean            # Realize function and simp lemmas
│   └── Operations.lean           # relabel, castLE, subst, FO embedding
└── Scott/
    ├── AtomicDiagram.lean        # AtomicIdx, atomicFormula, SameAtomicType
    ├── BackAndForth.lean         # BFEquiv predicate via Ordinal.limitRecOn
    ├── Formula.lean              # scottFormula construction
    ├── Sentence.lean             # scottSentence and main theorem
    └── Rank.lean                 # elementRank, scottRank, bounds
```

## Key Definitions

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

- **Relational languages** (`[L.IsRelational]`) - no function symbols
- **Countable languages** (`[Countable (Σ l, L.Relations l)]`)
- **Countable structures** (`[Countable M]`)

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
