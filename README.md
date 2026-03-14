# Infinitary Logic in Lean 4

![CI](https://github.com/cameronfreer/infinitary-logic/actions/workflows/build.yml/badge.svg)

A Lean 4 formalization of infinitary logic and Scott sentences, building on Mathlib. This project is under active development.

### Getting Started

```bash
git clone https://github.com/cameronfreer/infinitary-logic.git && cd infinitary-logic
lake build
pip install leanblueprint && leanblueprint web  # then open blueprint/web/index.html
```

## Main Results

1. **Scott Sentences** — Every countable structure in a relational countable language has a Scott sentence that characterizes it up to isomorphism.

2. **Scott Rank < ω₁** — The Scott rank of any countable structure is a countable ordinal.

3. **Karp's Theorem** — Back-and-forth equivalence at all ordinals characterizes infinitary elementary equivalence.

4. **Model Existence / Completeness** — Consistency properties yield models for Lω₁ω theories.

### Open Directions

- **López-Escobar Theorem** — Borel isomorphism-invariant sets of structures are Lω₁ω-definable.
- **Unconditional Morley-Hanf** — Remove the `MorleyHanfTransfer` hypothesis by formalizing Erdős-Rado / Ehrenfeucht-Mostowski machinery.
- **Admissible fragment completeness** — Full Barwise completeness beyond the schematic statement.

## Current Status

The project targets Lean 4 / Mathlib `v4.27.0`. There are currently **no `sorry` placeholders**
in `InfinitaryLogic/*.lean`.

> **Current Boundaries.** The remaining boundaries are mathematical scope rather than proof holes:
>
> - `CountableRefinementHypothesis` is proved internally and serves as an architectural
>   hinge — downstream results depend on it but the proof itself is complete.
> - `morley_hanf_of_transfer` is conditional on the explicit hypothesis
>   `MorleyHanfTransfer`, which packages deep Erdős-Rado / Ehrenfeucht-Mostowski machinery.
> - `morley_counting_dichotomy` is currently **schematic** (`True` in Lean) pending
>   descriptive set theory infrastructure; the intended statement is explained in
>   its docstring.

## Blueprint

The interactive blueprint with dependency graph is deployed at:

- **[Live Blueprint](https://cameronfreer.github.io/infinitary-logic/blueprint/)**
  (web, with dependency graph)
- **[Blueprint PDF](https://cameronfreer.github.io/infinitary-logic/blueprint/blueprint.pdf)**
- **[API Docs](https://cameronfreer.github.io/infinitary-logic/docs/)**
  (rebuilt weekly or on manual trigger)

A cached copy of the PDF is also committed at `blueprint/print/print.pdf`.

To regenerate locally:

```bash
lake build :blueprint          # extract .tex from Lean sources
lake build :blueprintJson      # extract .json for declaration linking
leanblueprint web              # → blueprint/web/ (generates lean_decls)
leanblueprint pdf              # → blueprint/print/print.pdf
lake exe checkdecls blueprint/lean_decls  # verify all blueprint nodes
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

- Barwise, J. (1975). *Admissible Sets and Structures*. Springer-Verlag.
- Karp, C. R. (1964). *Languages with Expressions of Infinite Length*. North-Holland.
- Karp, C. R. (1965). Finite-Quantifier Equivalence. In *The Theory of Models*, 407–412.
- Keisler, H. J. (1971). *Model Theory for Infinitary Logic*. North-Holland.
- Keisler, H. J. & Knight, J. F. (2004). Barwise: Infinitary Logic and Admissible Sets.
  *Bulletin of Symbolic Logic*, 10(1), 4–36.
- Marker, D. (2016). *Lectures on Infinitary Model Theory*. Cambridge University Press.
- Nadel, M. E. (1974). Scott sentences and admissible sets.
  *Annals of Mathematical Logic*, 7(2–3), 267–294.

## License & Citation

Apache 2.0 licensed. See [LICENSE](LICENSE) for more information.

Citing this repository is highly appreciated but not required by the license. See also [CITATION.cff](CITATION.cff).

```bibtex
@software{freer2026infinitary,
  author = {Cameron Freer},
  title = {Infinitary Logic in {Lean} 4},
  url = {https://github.com/cameronfreer/infinitary-logic},
  year = {2026}
}
```
