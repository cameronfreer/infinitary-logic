# Craig interpolation (#8): statement-and-interface audit

Pre-implementation audit for issue #8, in the pattern of `docs/fragments-audit.md`. No Lean is
written here; the deliverable is a frozen headline statement, a field-by-field verdict on the
existing Henkin interface, the two genuinely new prerequisites the issue does not anticipate,
and the decision points that need review before proof construction.

Sources: Marker, *Lectures on Infinitary Model Theory*, Theorem 4.20 (§4.3); Keisler, *Model
Theory for Infinitary Logic*, Chapter 3 (consistency properties over pairs, inseparability).

## 1. Scope

- **In scope**: the interpolation theorem for `L_ω₁ω` sentences, the fragment-relative
  model-existence interface (`ConsistencyPropertyEqOn`) that carries it, the inseparability
  closure lemmas, and the PC-separation corollary statement shape.
- **Out of scope**: undefinability of well-ordering (separate issue per #8's body); the
  PC-class representation freeze and the invariant-Borel-to-PC audit (those are #10
  reconnaissance, run separately); the hard direction of López–Escobar.

## 2. The frozen headline statement

```
theorem craig_interpolation {L : Language.{0,0}} (φ₁ φ₂ : L.Sentenceω)
    (h : Sentenceω.Entails φ₁ φ₂) :
    ∃ θ : L.Sentenceω,
      Sentenceω.Entails φ₁ θ ∧ Sentenceω.Entails θ φ₂ ∧
      θ.functionsIn ⊆ φ₁.functionsIn ∩ φ₂.functionsIn ∧
      θ.relationsIn ⊆ φ₁.relationsIn ∩ φ₂.relationsIn
```

with the symbol-occurrence sets of `Methods/GeneratedSublanguage.lean`, exactly as the issue
froze them. Notes on the conclusion:

- Equality is a logical symbol: `BoundedFormulaω.equal t u` contributes `t.functionsIn ∪
  u.functionsIn` and no relation symbol, so `θ = ⊥` and equality-only interpolants are
  admissible — the degenerate cases (φ₁ unsatisfiable ⟹ θ = ⊥; ¬φ₂ unsatisfiable ⟹ θ = ⊥.not)
  fall out of the construction with empty occurrence sets.
- **No ambient countability hypothesis** on `L` in the headline: each sentence mentions only
  countably many symbols (`functionsIn_countable`, `relationsIn_countable`), and the proof runs
  inside `symbSublang (φ₁.functionsIn ∪ φ₂.functionsIn) (φ₁.relationsIn ∪ φ₂.relationsIn)`,
  transported back by `mapLanguage_restrictSymbols` + `realize_mapLanguage_of_injective`
  (issue milestone 2). The countable core theorem carries the countability instances.

### D1 — the entailment definition (new; nothing in the tree defines ⊨ between sentences)

Recommended freeze:

```
def Sentenceω.Entails (φ ψ : L.Sentenceω) : Prop :=
  ∀ (M : Type) [L.Structure M], Sentenceω.Realize φ M → Sentenceω.Realize ψ M
```

- **Carriers at `Type 0`**, matching the `ScottCompletion.lean` precedent
  (`Lomega1omegaComplete` quantifies `Type` carriers) and matching where the contradiction
  model lives (the Henkin term model over a `{0,0}` language is a `Type 0` quotient; the
  symbSublang expansion `expandSymbStructure` keeps the same carrier). A `Type 0`-carrier
  hypothesis is the weakest usable hypothesis, and the produced entailments are proved
  semantically step-by-step, so nothing stronger comes out; universe generalization (via
  `ULift` + `realize_equiv` transfer) is a later cosmetic layer if ever wanted, not part of
  this arc.
- **Empty carriers allowed** (no `Nonempty M`). The contradiction step only consumes the
  hypothesis at the (nonempty) term model, so admitting empty carriers weakens the hypothesis
  for free. Risk is confined to the closure-lemma entailment facts; each is verified as it is
  proved, and if a base case genuinely breaks over the empty structure, `Nonempty` is added
  uniformly to `Entails` — a one-line change at the definition, flagged now so it is a known
  fallback rather than a mid-proof surprise.

## 3. Symbol-occurrence API inventory — COMPLETE, no gaps

`Methods/GeneratedSublanguage.lean` (pinned `Language.{0,0}`, consistent with D1) already has
everything the statement and the milestone-2 reduction need:

| Need | Have |
|---|---|
| occurrence sets | `Term.functionsIn`, `BoundedFormulaω.functionsIn`, `BoundedFormulaω.relationsIn` |
| countability | `functionsIn_countable`, `relationsIn_countable` |
| two-sorted sublanguage | `symbSublang F R`, `symbSublangIncl` |
| sublanguage countability | `symbSublang_fun_countable`, `symbSublang_rel_countable` |
| restriction | `Term.restrictSymbols`, `BoundedFormulaω.restrictSymbols` |
| round-trip | `mapLanguage_restrictSymbols`, `onTerm_restrictSymbols` |
| realization transfer | `realize_mapLanguage_of_injective` (Operations.lean:652), `expandSymbStructure` (MorleyHanfSchemaDischarge.lean:63 — should be MOVED to a Methods/ file when consumed here; `Conditional/` is the wrong home for a dependency of an unconditional headline) |

The only new occurrence-level lemma needed: `functionsIn`/`relationsIn` of the *constructed*
interpolant, which is handled structurally — the closure lemmas carry the separator's
occurrence bound as an invariant (§7), so no posthoc occurrence computation is required.

## 4. The Marker/Keisler route mapped to the repository

Fix `L₁ = symbols of φ₁`, `L₂ = symbols of φ₂`, `L₀ = L₁ ∩ L₂` (as occurrence-set pairs, not
new `Language` values, until the final symbSublang packaging). Add fresh constants: work in
`L' = (symbSublang (F₁ ∪ F₂) (R₁ ∪ R₂))[[ℕ]]` with `Sent₁ = sentences whose symbols lie in
L₁ + constants`, `Sent₂` likewise for `L₂`, `Sent₀` for `L₀`.

1. `Insep Γ Δ` : no σ with symbols in `L₀` + constants such that `Γ ⊨ σ` and every model of
   `Δ` refutes σ. (Pairs `Γ ⊆ Sent₁`, `Δ ⊆ Sent₂`.)
2. If φ₁ has no interpolant, `({φ₁}, {¬φ₂})` is inseparable *with constant-free separators*;
   a preliminary lemma upgrades this to inseparability with constant-allowing separators
   (constants can be generalized away — §6).
3. The inseparable pairs form a fragment-relative consistency property on
   `U = Sent₁ ∪ Sent₂` (the closure lemmas, §7).
4. Fragment-relative model existence (§5) yields `M ⊨ φ₁ ∧ ¬φ₂`, contradicting `φ₁ ⊨ φ₂`.

## 5. Field-by-field audit of `ConsistencyPropertyEq` — and the load-bearing finding

Verdicts against `Methods/Henkin/ConsistencyProperty.lean`, for the inseparability instance:

| Field | Quantification | Verdict |
|---|---|---|
| `C0_no_falsum`, `C0_no_contradiction` | members only (C0b's ∀φ is negative) | **fragment-safe as stated** |
| `C1`, `C1'`, `C2`, `C3`, `C3'`, `C4`, `C4'` | decompose members | **fragment-safe as stated** — components of a `U`-sentence stay in `U` |
| `extension` | **∀ φ : Sentenceω** | **BROKEN** (the issue's "hidden prerequisite"): mixed sentences with private symbols from both sides can be added to neither coordinate. Restriction to `∀ φ ∈ U` is provable for inseparability (θ₁ ∨ θ₂ combination) — but see D5: the forward-only truth lemma may not need it at all. |
| `chain_closure` | arbitrary ⊆-chains | **FALSE for inseparability — see Finding 1.** Must be dropped from the interface, not restricted. |
| `C5_eq_refl` | **∀ t : closed L-term** | **BROKEN**: closed terms over the joint language mix private function symbols from both sides; `t = t` for a mixed `t` is in neither `Sent₁` nor `Sent₂`. Restrict to a designated witness-term supply `T` (§8). |
| `C6_eq_subst` | ∀ t₁ t₂ closed, **∀ φ : Formulaω (Fin 1)** | **BROKEN twice**: terms as in C5, and the substitution template φ must have its instances in `U`. Restrict both. |
| `C7_quantifier`, `C7_neg_all` (∃-witness forms) | witness `∃ t` | safe if the interface *produces* witnesses in `T` — for the instance the witnesses are the fresh constants, which are shared, so `φ(c)` stays on φ's side. Strengthen the conclusion to `∃ t ∈ T`. |
| `C7_all`, `C7_neg_ex`, `C7_all_bound`, `C7_neg_all_bound` | **∀ t closed** | **BROKEN** as in C5: restrict to `∀ t ∈ T`. |

### Finding 1 (load-bearing): `chain_closure` is false for inseparability, so the Zorn route is unusable

`L_ω₁ω` entailment is not compact, and separability of a union does not descend to a chain
stage. Concrete refutation, entirely inside a common vocabulary `{0, S, c}` (so it applies to
any fragment-relative generalization, not just an unlucky side-split):

- `Γₙ = { ¬(c = Sᵏ0) : k < n }`, `Δ = { ¬θ }` where `θ = ⋀ₖ ¬(c = Sᵏ0)`.
- Each `(Γₙ, Δ)` is inseparable: the structure `ℕ` with `c := n` models `Γₙ` and refutes θ,
  so no σ with `Γₙ ⊨ σ ⊨ θ` exists.
- The union pair `(⋃ₙ Γₙ, Δ)` is separated by `σ = θ` itself.

Consequently `ConsistencyProperty.exists_maximal` (Zorn over `chain_closure`,
`Construction.lean:63`) cannot be instantiated, and the entire existing pipeline
`exists_maximal → MaximalConsistent → truthLemma` is unavailable *as a pipeline*. This is why
Keisler's model existence theorem hypothesizes a **countable** starting set and only one-step
closure conditions: the correct construction is a countable **enumeration** (Henkin priority
argument), not a maximality argument. The issue's phrase "adapting the existing Henkin
construction" therefore means: re-host `TermModel` + `truthLemma` on a new completion
predicate, and build that predicate by enumeration. Refactor plan in §6.

## 6. Construction refactor plan (milestone 1) and Finding 2

### 6a. Re-hosting the term model and truth lemma

Introduce a predicate capturing exactly what `truthLemma` consumes — the per-connective
membership-closure properties currently derived from `MaximalConsistent` at
`Construction.lean:90–176` — relative to `U` and `T`:

```
structure HenkinComplete (U : Set L.Sentenceω) (T : Set (L.Term Empty)) (S : Set L.Sentenceω)
```

with fields: S ⊆ U; no falsum; no contradiction pair; if `φ.imp ψ ∈ S` then `φ.not ∈ S ∨ ψ ∈ S`
(and the dual); iInf/iSup component membership (and duals); `t = t ∈ S` for `t ∈ T`;
C6-substitution closure over `T`; ∃-members have a witness instance in `S` at some `t ∈ T`
(and the three dual/universal forms over `T`).

- `TermModel` is rebuilt with carrier `T / ∼` (quotient of the designated supply, not of all
  closed terms — in the relational core `T` = the fresh-constant terms, so the carrier is
  countable by construction and function symbols never produce mixed terms).
- `truthLemma` becomes **forward-only, both polarities, simultaneously**:
  `φ ∈ S → M ⊨ φ` and `φ.not ∈ S → ¬ M ⊨ φ`, by the existing Ordinal-`depth` termination
  measure (the `not = imp falsum` wrinkle is already solved there). Forward-only is all that
  model existence needs (`{φ₁, ¬φ₂} ⊆ S ⊆ S*`), and it is what drops `extension` (D5).
- The existing endpoints (`model_existence`, `model_existence_uncountable_language`) are
  preserved untouched by a bridge lemma `MaximalConsistent → HenkinComplete Univ Univ` — the
  old Zorn route keeps serving the old consumers; nothing downstream moves.

### 6b. The enumeration construction

`henkinComplete_of_consistencyPropertyEqOn`: given `ConsistencyPropertyEqOn U T` (§8), `U`
countable, `T` countable, `S₀ ∈ sets` countable, produce `S* ⊇ S₀` with
`HenkinComplete U T S*`. One ω-recursion over a surjection `ℕ → (tasks)`, where the task list
schedules, each infinitely often: decompose-if-member for each `U`-sentence, add `t = t` for
each `t ∈ T`, C6 instances, and witness extraction for ∃-members. Every stage stays in `sets`;
the union satisfies `HenkinComplete` because each pair of offending members already cohabits
some stage (directedness), never because the union is in `sets` — that is exactly the property
Finding 1 kills, and it is not needed.

### Finding 2: constant abstraction is a missing syntactic operation

The C7 inseparability-closure lemma turns a separator `σ(c)` of `(Γ ∪ {φ(c)}, Δ)` into the
separator `∃x σ(x)` of `(Γ ∪ {∃x φ}, Δ)` — one fresh constant is *withdrawn into a quantifier*.
The tree has substitution (`subst`, var → term) but **no inverse**: no operation replaces a
constant symbol by a variable anywhere in `InfinitaryLogic/`. Needed, on `L[[ℕ]]` (constants =
`Sum.inr` nullary functions):

```
def BoundedFormulaω.abstractConstant (j : ℕ) :
    L[[ℕ]].BoundedFormulaω α n → L[[ℕ]].BoundedFormulaω (α ⊕ Fin 1) n
```

(term-level recursion replacing `func (Sum.inr j) ![]` by the new free variable, other
constants kept), with the realize lemma (`realize (abstractConstant j φ) v[x := cᴹ] ↔ realize
φ v`), the round-trip against `subst`, an occurrence lemma (`(abstractConstant j φ).functionsIn
⊆ φ.functionsIn \ {c_j}` in the appropriate sense), and the semantic generalization lemma:
if `Γ ⊨ σ(c)` and `c` does not occur in Γ, then `Γ ⊨ ∃x σ(x)` — proved by reinterpreting `c`
(a structure-surgery argument: modify only the constant's interpretation, realize of
constant-free sentences unchanged). This is the subtlest genuinely new syntax-level unit of
the arc; it also yields, iterated, the step-2 preliminary lemma of §4 (constant-free
inseparability upgrades to constant-allowing inseparability at the root pair, since φ₁, ¬φ₂
are constant-free).

## 7. The inseparability closure lemmas (user step 3)

One lemma per interface field, each with the *separator-combination* content:

| Field | separator combination |
|---|---|
| C1/C1'/C2 dichotomies | `σ₁ ∨ σ₂` (side 1) / `σ₁ ∧ σ₂` (side 2) |
| C3, C4' (∀-shaped, per-k) | separator unchanged |
| C3', C4 (∃-shaped: some k) | `⋁ₖ σₖ` resp. `⋀ₖ σₖ` — **the essential `L_ω₁ω` step**: countably many per-disjunct separators recombine by a countable connective. This is where interpolation is true for `L_ω₁ω` and false for finitary logic relative to infinitary classes. |
| C5/C6 | separator unchanged (equality steps happen within one side; `T`-terms are common-vocabulary) |
| C7 family | `∃x σ(x)` via `abstractConstant` (Finding 2) |
| extension-on-U (if kept, D5) | `σ₁ ∨ σ₂` |

**D4 — dualization.** `Insep` is symmetric under `(Γ, Δ) ↦ (Δ, Γ)` with `σ ↦ σ.not` (up to a
double-negation realize lemma). Freeze: prove each closure lemma for side 1 only and derive
side 2 through the swap lemma — halves the connective-by-connective work and keeps the
side-2 statements from drifting.

The occurrence bound on the final interpolant is carried by `Insep`'s definition itself
(separators are quantified over `Sent₀`-sentences), so the headline's `functionsIn/relationsIn`
conclusions need no separate bookkeeping — only the root-pair upgrade of §6's generalization
lemma (constants out) and the symbSublang round-trip (milestone 2) touch the occurrence sets.

## 8. The frozen interface (user step 2, principal correctness gate)

```
structure ConsistencyPropertyEqOn (U : Set L.Sentenceω) (T : Set (L.Term Empty)) where
  sets : Set (Set L.Sentenceω)
  subset_U : ∀ S ∈ sets, S ⊆ U
  -- C0a, C0b, C1, C1', C2, C3, C3', C4, C4' verbatim from ConsistencyProperty
  -- C5, C6, C7_all, C7_neg_ex, C7_all_bound, C7_neg_all_bound: term quantification ∀ t ∈ T
  -- C6: substitution templates restricted to instances-in-U
  -- C7_quantifier, C7_neg_all(_bound): conclusion strengthened to ∃ t ∈ T
  -- NO extension field (D5), NO chain_closure field (Finding 1)
```

No separate `U`-closure structure: each field's conclusion `S ∪ {x} ∈ sets` forces `x ∈ U`
through `subset_U`, so closure of `U` is a *consequence of instantiability*, checked once when
the inseparability instance is built (where `U = Sent₁ ∪ Sent₂` is closed under components,
negations of components, and `T`-instantiation by inspection of the occurrence sets).

**D5 — drop `extension` entirely (recommended).** The forward-only truth lemma (§6a) never
needs `S*` to decide anything: negative information flows through the dual fields and C0.
Marker's θ₁∨θ₂ extension lemma is real mathematics, but nothing in this arc consumes it; if a
later consumer (e.g. a fragment-relative completeness statement) wants deciding completions,
extension-on-U can be added then, together with its closure lemma. Leaner gate now.

**D3 — pair representation (recommended: existential-pair form).**
`sets = { S | ∃ Γ Δ, S = Γ ∪ Δ ∧ Γ ⊆ Sent₁ ∧ Δ ⊆ Sent₂ ∧ Insep Γ Δ }`. The canonical-split
alternative (`Insep (S ∩ Sent₁) (S ∩ Sent₂)`) is *strictly stronger* on the overlap (`Sent₀`
sentences from Δ migrate into the first coordinate, enlarging the entailment premises), so the
field verifications would prove statements Marker's lemmas don't give. Every field only needs
to exhibit *some* witness split for the output set, which the existential form does natively.

**Countability of `U`.** For the instance, `U` is generated from `{φ₁, ¬φ₂}` by components,
negation, and `T`-instantiation. Components of an `L_ω₁ω`-formula form a countable set
(countably-branching well-founded tree — same argument as `functionsIn_countable`), and
`T ≃ ℕ`, so `U` is countable. Reuse the `List`-path-encoding countability technique of
`Fragment.generated_countable` in spirit; the #13 `Fragment` structure itself is NOT the host
(it deliberately excludes substitution closure — `Fragment.lean:17` — and lives at
`BoundedFormulaω Empty n` across arities, while `U` is a sentence set over `L[[ℕ]]`).

## 9. Relationalization boundary (user step 6)

The core runs with `T` = fresh-constant terms only, which is fully general **only for
relational `L₁, L₂`** (no mixed terms exist, and the term-model carrier `T/∼` interprets no
function symbols). Freeze: the core theorem is
`craig_interpolation_relational : [(symbSublang …).IsRelational-style hypotheses] → …` at
countable symbol sets, then milestone 2 removes ambient countability via symbSublang, and
**relationalization is a separate final layer** translating function symbols to graph
relations (a new, self-contained syntactic translation with a realize bridge — not started
until the relational core is stable, per direction). Note: the headline as frozen in §2 (with
`functionsIn` in the conclusion) is delivered only after this layer; the intermediate
relational endpoint is the arc's first publishable theorem and gets the blueprint node.

## 10. PC-separation corollary (kept in #8; consumed by #10)

Shape to deliver (exact `Language`-inclusion packaging to be frozen in the #10 reconnaissance,
which owns the PC-class representation):

> If `ψ₁ ∈ L₁.Sentenceω` and `ψ₂ ∈ L₂.Sentenceω` have no common model on the shared
> vocabulary `L₀` (no `L₀`-structure expands to both a model of ψ₁ and a model of ψ₂), then
> some `θ ∈ L₀.Sentenceω` holds in every `L₀`-reduct of a model of ψ₁ and fails in every
> `L₀`-reduct of a model of ψ₂.

Derivation: apply interpolation to `ψ₁ ⊨ ¬ψ₂` in the joint vocabulary; θ's symbols land in
the intersection; restrict by `restrictSymbols` + transfer by `expandSymbStructure`. The only
#8-side commitment this makes: the corollary is stated over the two-sorted `symbSublang`
representation of "shared vocabulary" — consistent with the milestone-2 machinery and with
what `MorleyHanfSchemaDischarge` already does; #10 can re-package.

## 11. Unit sequencing (maps to the six agreed steps)

1. **Statement layer**: `Sentenceω.Entails` (D1) + `docs` this audit; move
   `expandSymbStructure` out of `Conditional/`.
2. **Interface**: `ConsistencyPropertyEqOn U T` + `HenkinComplete` + bridge from
   `MaximalConsistent` (old endpoints untouched) + re-hosted `TermModel`/forward truth lemma
   (§6a) + enumeration construction (§6b). *Gate: fragment-relative model existence proved.*
3. **Syntax unit**: `abstractConstant` + realize/occurrence/round-trip + semantic
   generalization lemma (Finding 2).
4. **Inseparability**: definition, swap lemma (D4), closure lemmas connective-by-connective
   (§7), the instance of the §8 interface.
5. **Endpoints**: relational-countable core → symbSublang generalization → headline
   `craig_interpolation` (relational) + PC-separation corollary.
6. **Relationalization layer** (separate, last).

## 12. Decision points for review

| # | Decision | Recommendation |
|---|---|---|
| D1 | `Entails` carriers | `Type 0`, no `Nonempty` (fallback flagged) |
| D2 | universe scope | pin `Language.{0,0}` for the whole arc (GeneratedSublanguage already is) |
| D3 | pair representation in `sets` | existential-pair form |
| D4 | side-2 closure lemmas | via the `Insep`-swap lemma, not re-proved |
| D5 | `extension` field | dropped; forward-only truth lemma |
| F1 | Zorn/`chain_closure` | unusable (refuted §5); enumeration construction |
| F2 | `abstractConstant` | new syntax unit, scheduled before the closure lemmas |
