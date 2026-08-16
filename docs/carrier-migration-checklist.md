# Fixed-carrier migration: exit conditions and remaining tranches

Branch-local to `api/fixed-carrier-migration`. **Delete this file at the final deletion
checkpoint** — it describes work in progress, not the project's architecture.

## Exit conditions (must hold before this branch merges)

Both are recorded as prose now and enforced mechanically at the final deletion checkpoint, not
before: a guard added today would fail on every intermediate commit and train people to ignore it.

**E1 — no `*Legacy` surface remains.** `BoundedFormulaInfLegacy`, `FormulaInfLegacy` and
`SentenceInfLegacy` were introduced by `c35b794` purely to let the project's own per-node-index
syntax coexist with Mathlib's carrier-fixed one during the migration. They are branch-local and
must reach zero occurrences.

**E2 — `TheoryInf` must no longer hide a legacy sentence type.** `Linf/Theory.lean:47` currently
reads `abbrev TheoryInf (L) := Set L.SentenceInfLegacy`. Throughout the migration it may keep
meaning that; at merge it must denote a Mathlib-backed sentence type, and no declaration on the
default import surface may depend on `SentenceInfLegacy`. E2 is not implied by E1: a rename that
left `TheoryInf` pointing at a surviving legacy definition would satisfy a naive occurrence count
while preserving exactly the dependency this condition exists to remove.

### The check to add at the deletion checkpoint

A zero-occurrence check over the Lean tree, not a prose review:

```
grep -rn 'BoundedFormulaInfLegacy\|FormulaInfLegacy\|SentenceInfLegacy' --include=*.lean InfinitaryLogic/
```

must return nothing, and `TheoryInf`'s definition must be inspected directly rather than inferred
from that count. Wire it into `scripts/` alongside the existing boundary guards only once it can
pass.

## Current surface (measured 2026-08-16 at `2ba7b17`)

| Name | Occurrences | Files |
|---|---:|---:|
| `BoundedFormulaInfLegacy` | 270 | 11 |
| `FormulaInfLegacy` | 68 | 7 |
| `SentenceInfLegacy` | 44 | 7 |
| `TheoryInf` | 10 | 1 |

Carrying files: `Core.lean`, `Karp/Theorem.lean`, `Linf/{Syntax,Semantics,Operations,Countability,QuantifierRank,Theory}.lean`,
`Lomega1omega/Embedding.lean`, `ModelTheory/TypePreservingBF.lean`, `Scott/QuantifierRank.lean`.

## Next tranche

Begins with a fresh audit of every remaining `*Legacy` reference, each classified into exactly one
of three buckets — the classification is the deliverable, not a by-product:

1. **Obsolete — delete.** Unused theory-level and lift machinery superseded by `reindex`.
2. **Genuine carrier-parametric operations — port** to `BoundedFormulaInf L ι`.
3. **Karp's mixed-index construction — replace** with the already-proved common-carrier
   formulation (`karp_theorem_at`, canonical carrier `M ⊕ N`).

Then: port Karp, add its headline/axiom check and a correctly implemented dependency-cone guard,
and delete the old per-node syntax once its final consumer disappears.
