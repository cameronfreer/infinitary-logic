# Back-and-forth API audit (issue #17, step 1 — the frozen interface decision)

Decides the semantic acceptance target for the small-model → complete-sentence chain, before
any proof code. *(#17's first gate, part 1; part 2 is the isolator characterization.)*

## 1. The existing relations

| Relation | Shape | Where |
|---|---|---|
| `BFEquiv α n a b` | ordinal-indexed, TUPLE-indexed Prop: atomic agreement at 0, forth/back at successors, conjunction at limits | `Scott/BackAndForth.lean` (blueprint node `def:BFEquiv`) |
| `PotentialIso L M N` | bundled STRUCTURE: a nonempty family of finite partial correspondences with forth/back | `Karp/PotentialIso.lean` |

Existing bridges (both under `[Countable (Σ l, L.Relations l)]`):
`PotentialIso.implies_BFEquiv_all` and `BFEquiv_all_implies_potentialIso` — and the latter's
proof exhibits the canonical extension family as exactly `{p | ∀ α, BFEquiv α p.1 p.2.1 p.2.2}`.

## 2. The audit questions

**(a) Weakest relation supporting finite tuple extensions.** `∀ α, BFEquiv α n a b` — it is
tuple-indexed (precisely the shape of #17 step 4's relation between `ā ∈ M` and `b̄ ∈ N`), its
successor clauses ARE the forth/back extension property, and the existing
`BFEquiv_all_implies_potentialIso` shows it generates the canonical partial-correspondence
family. `PotentialIso` is strictly stronger packaging (a chosen family), needed only for the
countable-countable isomorphism endpoint (`PotentialIso.countable_toEquiv`).

**(b) Connection to all-infinitary-formula invariance.** `BFEquiv_implies_agreeQR`
(`Karp/Theorem.lean`): `BFEquiv α` transfers every `BoundedFormulaInf` of quantifier rank
`≤ α`; at all `α`, all of `L_∞ω`. Only this forward direction is needed (the reverse was the
deleted legacy `agree_implies_BFEquiv`; `karp_theorem_w` routes through `LinfEquivW` and is not
on this path). `Sentenceω`-equivalence is the rank-bounded specialization.

**(c) Does Scott-sentence categoricity already consume it?** YES, natively:
`scottSentence_characterizes_of` runs on `realize_scottFormula_iff_BFEquiv` plus the (proved)
`CountableRefinementHypothesis` stabilization — the Scott stack's interface IS `BFEquiv`.
`PotentialIso` does not appear anywhere on the Scott path.

**(d) Thin bridge?** Neither relation is replaced and no new acceptance structure is defined.
ONE thin bridge lemma is added, in the direction the isolators feed:

> **`bfEquiv_all_of_typePreservingFamily`** *(name provisional)*: if `R` is a relation between
> `M`-tuples and `N`-tuples (same arity) such that (i) `R`-related tuples have the same
> `L_ω₁ω`-type over the ambient structure, and (ii) `R` has the forth and back extension
> properties, then `R`-related tuples are `BFEquiv α` for every `α` — one ordinal induction
> (`limitRecOn`): zero needs type agreement ⇒ `SameAtomicType` (atomic formulas are
> `L_ω₁ω`-formulas — a small `SameAtomicType`-bridging lemma alongside), successor is (ii),
> limit is trivial.

## 3. The frozen decision

- **Semantic acceptance target: `∀ α, BFEquiv α`** between the small model and the companion —
  at the empty tuple for the structure-level theorem, tuple-level for the back-and-forth.
- Step 4's relation is the isolator-induced **type-agreement family** (viewing companion
  tuples in the ambient `M`); step 5 proves it satisfies (i)+(ii) and applies the bridge, then
  derives `L_∞ω`- (hence `Sentenceω`-) equivalence via `BFEquiv_implies_agreeQR`.
- Step 6 hands `BFEquiv`-all directly to the Scott stack — no adapter.
- `PotentialIso` is NOT a target; if a consumer ever wants it, the existing
  `BFEquiv_all_implies_potentialIso` already converts.

## 4. Scope finding (inherited hypotheses)

The entire Scott/Karp stack is stated under **`[L.IsRelational]`** (and
`[Countable (Σ l, L.Relations l)]` where counting matters; CRH is proved, not assumed). So
#17's companion/complete-sentence chain is for **countable relational vocabularies** — the
issue's countable-symbol hypothesis PLUS relationality, both inherited, neither new. The
arbitrary-language form would require a relationalization construction (function graphs) that
does not exist in the repository; it is explicitly deferred (it is the same missing wrapper
flagged in #14/#15), NOT silently claimed. The #11 inputs (`Lomega1omegaSmall`,
`exists_small_model_of_hasArbLargeModels`) and the #13 inputs are language-general and
specialize without loss.
