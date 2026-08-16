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

## Dependency table (re-audited 2026-08-16, at `36e7250`)

### The gate does NOT pass as stated

The intended gate was: *every surviving `toLinf` use lies in the legacy rank bridge, and every
non-rank consumer reaches fixed-carrier syntax directly.* Measured, there are **two** consumers
outside the defining files, not one:

| Consumer | Kind | Reaches fixed-carrier syntax? |
|---|---|---|
| `Scott/QuantifierRank.lean:158` | rank bridge — feeds `φ.toLinf` into `BFEquiv_implies_agreeQR` | no, and by design until the rank layer lands |
| `Karp/CountableCorollary.lean:61` | `countable_LinfEquiv_implies_iso_of` | **no** — this is the gate failure |

The second is not a rank use. It converts `LinfEquiv → LomegaEquiv` by mapping each `Sentenceω`
through `toLinf`, inside a theorem whose *hypothesis* is the legacy `LinfEquiv`. It is the same
shape as the `ScottCompletion` detour just removed, and has the same one-line fix: restate the
hypothesis as `InfEquivW` (or `InfEquivAt L ℕ`) and the body collapses, because
`InfEquivAt L ℕ` and `LomegaEquiv` are the same proposition. Doing that first would let the gate
pass honestly instead of being weakened to accommodate the site.

### Measured dependencies

**`toLinf` / `realize_toLinf`** — defined in `Lomega1omega/Embedding.lean` (the ω family) and
`Linf/Operations.lean` (the finitary family). The finitary family has **zero** consumers
anywhere. The ω family has the two above.

**Importers of `Lomega1omega.Embedding`**: `Scott/QuantifierRank.lean`,
`Karp/CountableCorollary.lean`, and `Core.lean` (bundle).

**Consumers of `BFEquiv_implies_agreeQR`**: `Scott/QuantifierRank.lean:158` (through `toLinf`)
and `ModelTheory/TypePreservingBF.lean:177` (directly, on a legacy formula — no `toLinf`).

**Importers of `Karp.Theorem`**: `Core.lean`, `Scott/QuantifierRank.lean`,
`ModelTheory/TypePreservingBF.lean`, and `Karp/CountableCorollary.lean` — where the import is
now **stale**: it uses nothing from the file.

### Remaining legacy declarations, grouped

| Group | Decls | Occurrences | Files |
|---|---:|---:|---|
| core legacy syntax | 67 | 153 | `Linf/{Syntax,Semantics,Operations,Theory}.lean` |
| rank | 36 | 62 | `Linf/QuantifierRank.lean`, `Karp/Theorem.lean`, `Scott/QuantifierRank.lean`, `ModelTheory/TypePreservingBF.lean` |
| countability + `toLinf` | 22 | 46 | `Lomega1omega/Embedding.lean` |
| countability | 11 | 21 | `Linf/Countability.lean` |
| bundle | 1 | 1 | `Core.lean` |

### Remaining sequence

1. Fix the `CountableCorollary` gate failure above (restate the hypothesis as `InfEquivW`).
2. Re-check the gate; it should then pass with the rank bridge as the sole `toLinf` consumer.
3. Stage the rank module on top of PR2.
4. Port `BFEquiv_implies_agreeQR`, Scott rank, and `TypePreservingBF`.
5. Delete `toLinf` and the remaining legacy Karp file.

### What the rank tranche removes, once the gate passes

`BFEquiv_implies_agreeQR` and its supporting legacy induction; the `toLinf` family with its
realization and rank lemmas; and the remaining contents of `Karp/Theorem.lean`, letting that
module disappear.

`Lomega1omega/Embedding.lean` does **not** disappear with it: it also owns the deferred
`ofCountable` cluster. Trim it to countable recovery, or rename/split it when the countability
layer is ported — do not delete it merely because its `toLinf` half became obsolete.

## Deferred: one bounded documentation commit, near the end of the migration

Not provenance infrastructure — no `SOURCE_PROVENANCE.md`. Three separate tracks:

1. **Blueprint bibliography** (`blueprint/src/refs.bib`). Verified state at `36e7250`: the file
   holds exactly `karp1965`, `scott1965`, `keisler1971`, `nadel1974`, `barwise1975`,
   `marker2016`; `content.tex` cites only `marker2016`, `karp1965`, `barwise1975`, `nadel1974`,
   `keisler1971`.
   - **Keisler–Knight 2004 is absent** (DOI `10.2178/bsl/1080330272`) while 25 `[KK04]` markers
     across 10+ modules refer to it and `CarrierTheorem.lean` names Theorem 1.2.1. Most
     immediate defect.
   - **`scott1965` is present but never cited.** Cite it in the Scott section as the original
     theorem, with Marker Ch. 2 as the modern exposition.
   - **Karp 1964 is absent** from `refs.bib` (the README has it); add alongside
     syntax/countability if that material gets a blueprint paragraph.
   - Expand the bare `[Karp65]`, `[KK04]` markers in `CarrierTheorem.lean`.
2. **Design credit**, in the migration PR and release notes only, not the README: the
   fixed-carrier formulation was suggested by Aaron Liu on Zulip and developed against Mathlib
   in PR #42758; infinitary-logic #43 records the downstream validation. Use exact permalinks.
3. **Not sources**: TauCetiRoadmap #41 (downstream planning), #43 (implementation evidence),
   and any AI tooling — the last is a development-assistance disclosure in the PR, not
   authorship. Malitz 1969 stays unverified; the audit records that the primary paper was never
   checked.

Module docs must not imply Karp stated the `IndexCoding` formulation. The mathematical
equivalence is Karp's theorem; "any common carrier equipped with codings" is this
formalization's API-level presentation of it. When the generalized Scott sentence moves from
the spike into production it is **new to this repository, not mathematically novel** — Scott
1965 for the countable theorem, Marker Ch. 2 (Thm 2.19) for the arbitrary-structure statement.

Unrelated to this migration, worth a later cleanup: López–Escobar 1965 is in the README but not
in `refs.bib`, and the blueprint's López–Escobar chapter has no citation.

### Dependency fence: quantifier rank is not in PR2

PR2 carries syntax, semantics and transport; it does **not** carry quantifier rank. So
`Scott/QuantifierRank.lean` has no upstream target in this tranche. Do not force it through, and do
not retain the legacy syntax merely to keep it compiling, without making that choice explicit and
recording it here. The expected route after Karp is a small stacked rank branch built on the
already-validated prototype (`qrank_reindex` up to `Ordinal.lift`, and the missing
`Ordinal.lift_iSup` it needs).
