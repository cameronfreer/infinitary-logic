# Migration: retirement of `Admissible/Barwise/ConsistencyBridge.lean`

Status: proposed breaking change, for review before any deletion is applied. No new
mathematics, no release accompanies the proposal.

## What is removed

The whole module `InfinitaryLogic/Admissible/Barwise/ConsistencyBridge.lean` and nothing else:

| Declaration | Kind | Blueprint node |
| --- | --- | --- |
| `BarwiseFragment L` (extends `FiniteCompactFragment L`; field `chain_closure_consistent`) | structure | — |
| `FullBarwiseFragment L` (extends `BarwiseFragment L`; field `complete`) | structure | `def:full-barwise-fragment` |
| `consistentSets P` | def | — |
| `consistencyPropertyOfFullFragment B : ConsistencyPropertyEq L` | noncomputable def | `thm:consistency-property-full-fragment` |
| `barwise_completeness_II_syntactic_full` | theorem | `thm:barwise-completeness-ii-syntactic` |
| two private helper lemmas | — | — |

`FiniteCompactFragment`, `AdmissibleFragmentCore`, `AdmissibleFragment`, `WithConstants`, and
the ambient-HF layer are **not** touched: they appear in the bridge's ancestry, but retirement
of the bridge is not a reason to remove them.

There are no theorem consumers of the removed declarations anywhere in the tree (audit of
2026-09-06). The live references are the bundle import, two docstring mentions, README, the
interface contract §8, `docs/leanarchitect-blueprint.md`, the bundle docstring, three blueprint
nodes with their generated-declaration entries, and the forbidden-name lists of four guard scripts.

## Why

`BarwiseFragment.chain_closure_consistent` asserts that unions of chains of `P`-consistent sets
are `P`-consistent. `scripts/check_chain_closure_counterexample.lean` proves this **false** for
`P = Set.univ` over the constants-expanded language with one unary relation and ℕ constants
(the ω-rule derives `⊥` from the union). Consequently `FullBarwiseFragment` is uninhabited **for
that language**; the proper-formula-set `BarwiseFragment` is not shown uninhabited, and no claim
is made for every language. The counterexample script stays, with its claim about the specified
language, and is unchanged mathematically.

The successor engine is the countable-completion kernel (`ConsistencyPropertyEqOn`, no
`extension`, no `chain_closure`), reached through `HenkinClosedMin`.

## Successor APIs, not equivalent replacements

Each successor changes the language, universe, or consistency hypothesis. No
hypothesis-transport theorem is supplied by this migration: callers must establish the chosen
successor's stated hypotheses. The interfaces and producers (`HenkinClosedMin`,
`Fragment.henkinClosure`) are listed separately from the relational model-existence theorems
that consume them.

| Retired | Successor | Language / universe | Consistency hypothesis |
| --- | --- | --- | --- |
| `BarwiseFragment L` as the consumer contract (an interface, not a theorem) | `HenkinClosedMin P` (`Admissible/Barwise/HenkinClosed.lean`), an interface on `P : Set L[[ℕ]].Sentenceω` | `L : Language.{0,0}`; the interface itself needs no relational or countability assumption | no chain closure; the kernel's negated-target closure only |
| `FullBarwiseFragment L` as a producer of the full universe (an interface) | `Fragment.henkinClosure S` (`Admissible/Barwise/HenkinClosure.lean`), a producer: a fragment of `L` with a `HenkinBasis`; its countability needs `[Countable (Σ l, L.Relations l)]` | `Language.{0,0}`; source fragment of `L`, universe expanded by ℕ constants | consistency is stated **in the constants-expanded universe** `(henkinClosure S).withNatConstantsSentences` |
| `consistentSets P` (the family of `P`-consistent subsets of `P`) | `HenkinClosed.aconsistentSets P` | `Language.{0,0}`; `P : Set L[[ℕ]].Sentenceω` | definitionally the same family shape (`S ⊆ P ∧ AConsistent P S`) over the constants-expanded language |
| `consistencyPropertyOfFullFragment B : ConsistencyPropertyEq L` | `HenkinClosedMin.consistencyPropertyEqOn : ConsistencyPropertyEqOn P` | `Language.{0,0}`, **relational** base (`[L.IsRelational]`) | family of `P`-bounded `P`-consistent sets; no extension field |
| `barwise_completeness_II_syntactic_full` (any `L : Language.{u,v}` with countable symbol sigmas; `B : FullBarwiseFragment L`; `T ⊆ B.formulas`, `T.Countable`, `AConsistent B.formulas T`; model in `Type u`) | `HenkinClosed.exists_countable_model_of_aconsistent` | `Language.{0,0}`, **relational** base, countable relation sigma; model is an `L[[ℕ]]`-structure on a `Type` with the constants present | `AConsistent P T` with `P` Henkin-closed and countable; no countability of `T` |
| same | `Fragment.exists_countable_model_of_aconsistent_withConstants` (`SourceFragment.lean`; retains the `HenkinBasis` hypothesis `hB`) and `_henkinClosure` (`HenkinClosure.lean`; basis discharged by the closure) | `Language.{0,0}`, relational, countable relation sigma; countable source fragment or countable seed; `L`-model recovered by reduct | consistency of `mapLanguage '' T` **in the expanded universe**, not of `T` in the base language |
| same | `Fragment.exists_countable_model_of_aconsistent_graphUniverse` (`GraphUniverse.lean`) | `Language.{0,0}`, **not necessarily relational**, both symbol sigmas countable | consistency of the graph theory **in the graph universe**; nothing transports consistency across relationalization |

None of the successors is stated under the retired theorem's hypothesis "`T` is `A`-consistent in
the base language over a full fragment". Where the retired structure was uninhabited (the
counterexample language) that hypothesis was impossible, and nothing is inferred from it here.

## Documentation changes

- README: the placeholder list no longer names `FullBarwiseFragment`.
- Interface contract §8: the ConsistencyBridge row is replaced by a retirement row; the
  proof-system boundary sentence lists the surviving legacy names.
- Blueprint: the three `\inputleannode`s are removed and replaced by prose recording the
  retirement and pointing at the successor **APIs** (this patch adds no successor nodes); the old
  completeness node is **not** retargeted to any successor theorem, since their assumptions
  differ materially. The three `blueprint/lean_decls` entries are removed in place, and
  `docs/leanarchitect-blueprint.md` no longer lists the three nodes.

## Guard changes

The retired names are dropped from the forbidden-name lists of the cone guards (their
existence checks would otherwise fail as `[STALE GUARD]`), and one authoritative guard,
`scripts/check_consistency_bridge_retired.lean`, asserts their absence: it imports the whole
`InfinitaryLogic.Admissible` bundle with an import-presence assertion, uses a single
environment-lookup helper for both a synthetic control declaration that must resolve and the
five retired public names that must not, so that deleting the control or reintroducing a name
fails the guard. The successor endpoints' assembly and cone checks stay in their own guards
(`check_henkin_closed_cone.lean` now imports `Admissible.Fragment` explicitly, which the bridge
used to supply transitively).

## Validation and falsification, to run on the applied patch

1. Full local gate (build of every bundle, all guards, `checkdecls` on the updated `lean_decls`).
2. `scripts/check_chain_closure_counterexample.lean` still passes with only `Soundness`
   imported.
3. Falsification of the retirement guard, twice: re-declare a constant named
   `FirstOrder.Language.consistentSets` in a scratch copy and confirm `[RETIRED NAME PRESENT]`;
   delete the control declaration from a scratch copy and confirm the positive control fails.
4. No-deploy docs dispatch on the branch: blueprint builds, the freshness step passes with the
   edited `lean_decls`.
5. `grep -rn "ConsistencyBridge\|FullBarwiseFragment\|BarwiseFragment\b"` over `InfinitaryLogic`,
   `scripts`, `docs`, `README.md`, `blueprint` returns only this migration note, the
   retirement guard's intentional name list, the counterexample script's historical wording,
   the contract's retirement row, and the proof-system guard's pointer to the retirement guard.

## Version

Removing published declarations is breaking regardless of internal consumers: the next tag
after this lands is a major version bump.
