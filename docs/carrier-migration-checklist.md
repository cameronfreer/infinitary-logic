# Fixed-carrier migration: exit conditions and remaining tranches

Branch-local to `api/fixed-carrier-migration`. **This file is temporary and is itself an exit
condition — see E3.** Its occurrence counts and sequencing are useful while the migration is in
flight and become branch archaeology the moment it lands, which is exactly the drift surface the
2026-08-02 documentation reduction removed from this repository.

## Exit conditions (must hold before this branch merges)

All three are recorded as prose now and enforced mechanically at the final deletion checkpoint, not
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

**E3 — this file is deleted.** It records branch-local migration state, not architecture. Nothing
in it should survive the merge: the counts go stale immediately, and the sequencing is settled once
executed. Delete it in the same commit that satisfies E1 and E2.

### The check to add at the deletion checkpoint

A zero-occurrence check over the Lean tree, not a prose review:

```
grep -rn 'BoundedFormulaInfLegacy\|FormulaInfLegacy\|SentenceInfLegacy' --include=*.lean InfinitaryLogic/
```

must return nothing, and `TheoryInf`'s definition must be inspected directly rather than inferred
from that count. Wire it into `scripts/` alongside the existing boundary guards only once it can
pass.

## Declaration-level audit (2026-08-16)

168 declarations mention a `*Legacy` type. **50 have no reference outside their defining file** —
searching the whole repository (library, `scripts/`, `blueprint/`) and counting dot-notation uses,
both of which the first pass missed: a library-only search wrongly reported `karp_theorem_w` dead
because its only consumers are `check_headline_axioms.sh` and the blueprint.

Occurrence counts are not a classification. `E2` was satisfied by *deleting* `TheoryInf`, and the
lift machinery that looked deletable turned out to be Karp-coupled — neither is visible in a count.

| File | legacy decls | no external reference |
|---|---:|---:|
| `Karp/Theorem.lean` | 18 | 12 |
| `Lomega1omega/Embedding.lean` | 22 | 11 |
| `Linf/Operations.lean` | 30 | 10 |
| `Linf/Countability.lean` | 11 | 8 |
| `Linf/QuantifierRank.lean` | 24 | 3 |
| `Linf/Semantics.lean` | 29 | 2 |
| `ModelTheory/TypePreservingBF.lean` | 4 | 2 |
| `Linf/Theory.lean` | 17 | 1 |
| `Linf/Syntax.lean` | 11 | 0 |
| `Core.lean`, `Scott/QuantifierRank.lean` | 2 | 1 |

### Done: dead theory machinery removed

- **`TheoryInf` and its whole API deleted** (`Model`, `Model.empty`, `Model.mono`, `Valid`,
  `Model.of_equiv`). Every one of its ten references was internal to `Linf/Theory.lean`; nothing in
  the repository consumed it. **E2 is now satisfied by deletion, not by porting** — the file is
  `L∞ω Elementary Equivalence` now, and `realize_equiv` stays because `LinfEquiv.of_equiv` and
  `LinfEquivW.of_equiv` use it.
- `forallLastVarInf` / `realize_forallLastVarInf` and `toSentenceInf` / `realize_toSentenceInf`
  deleted — dead, and not shared with anything live.

### Finding: the lift machinery is Karp-coupled, not unused

`liftUI` and `realize_liftUI` have exactly one consumer: `Karp/Theorem.lean:428`
(`LinfEquivW_implies_LinfEquiv`). `existsLastVarInf` / `realize_existsLastVarInf` likewise have
exactly one: Karp's backward direction (`:354`, `:391`) — the mixed-index construction itself. The
private helpers underneath (`insertLastBoundInf`, `realize_relabel_insertLastBoundInf_zero`,
`snoc_elim0_zero_inf`) serve that same ∃ path.

**So removing the lift machinery is a consequence of the Karp port, not a precursor to it.** Step 2
cannot retire it; step 3 will, and the deletion should land in the same commit that replaces the
mixed-index construction, so no intermediate commit carries a half-ported Karp.

### Not touched, and why

- `Linf/Countability.lean` (8 dead: `indexBound`, `isKappa_succ_indexBound`, `exists_isKappa`,
  `IsCountable.toIsKappa_aleph1`, …) and `Lomega1omega/Embedding.lean` (11 dead: the whole
  `ofCountable` cluster) belong to the countability layer, which — like rank — is **not in PR2**.
  Deleting them presumes a replacement that does not exist upstream yet.
- `emptyiSup` / `emptyiInf` and their realize lemmas: retained by an earlier decision — zero
  internal references does not prove zero external users.
- The 12 dead declarations in `Karp/Theorem.lean` are bucket 3; they go with the port.

## Next tranche

**Target: dead legacy API removal plus Karp. Not a mass `Legacy` → new-API replacement.**

1. **Classify declarations, not occurrences.** An occurrence count says nothing about whether a
   declaration has consumers. Each legacy declaration goes into exactly one bucket, and the
   classification is the deliverable:
   - **delete** — no consumer outside its defining file, or superseded outright;
   - **port** — a genuine carrier-parametric operation, to `BoundedFormulaInf L ι`;
   - **replace** — Karp's mixed-index construction, by the common-carrier formulation.

   All ten `TheoryInf` references are internal to `Linf/Theory.lean`, so that API is
   **deletion-first**: do not port it by default just because it exists.
2. **Remove** the genuinely unused legacy theory and lift machinery.
3. **Port Karp** to the common-carrier API via `IndexCoding`, keeping the canonical sum-carrier
   theorem as a corollary rather than as the primitive statement.
4. **Add Karp's guards**: the headline axiom check, and a theorem-body dependency-cone guard that
   includes a *positive* dependency assertion — a cone guard that only forbids is satisfied
   vacuously by a theorem that proves nothing.
5. **Reassess** the remaining legacy surface, then delete the old per-node syntax once its final
   consumer disappears.

### Dependency fence: quantifier rank is not in PR2

PR2 carries syntax, semantics and transport; it does **not** carry quantifier rank. So
`Scott/QuantifierRank.lean` has no upstream target in this tranche. Do not force it through, and do
not retain the legacy syntax merely to keep it compiling, without making that choice explicit and
recording it here. The expected route after Karp is a small stacked rank branch built on the
already-validated prototype (`qrank_reindex` up to `Ordinal.lift`, and the missing
`Ordinal.lift_iSup` it needs).
