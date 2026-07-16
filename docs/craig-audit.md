# Craig interpolation (#8): statement-and-interface audit (v2)

> **STATUS: COMPLETE (2026-07-16).** The arbitrary-language headline `craig_interpolation`
> (no hypotheses on `L`) is proved in `Methods/Interpolation/CraigArbitrary.lean` (blueprint
> node `thm:craig`), with the PC-separation form `craig_pcSeparation`; both are exposed on the
> default surface via `ModelTheory/CraigInterpolation.lean` and guarded by
> `scripts/check_headline_axioms.sh`. The §9b relationalization landed as gated Units 1–7:
> `GraphLanguage` (graph relations + shared-vocab identity `relSym_inter`),
> `Lomega1omega/FiniteQuantification` (existsBlock/forallBlock), `TermGraph`
> (context-polymorphic term flattening), `Relationalize` (formula translation + exact `relSym`
> occurrence identity), `GraphAxioms`/`GraphReconstruction` (totality+functionality, localized
> structure reconstruction), `BackTranslate` (graph atoms → function equations + preimage
> occurrence calculus), `CraigArbitrary` (algebraic assembly; reconstruction only in
> `entails_graphTranslation`). The relational core `craig_interpolation_relational`
> (`thm:craig-relational`) and `craig_pcSeparation_relational` remain as the internal core and
> the #10 deliverable respectively. Theorem-landing tag: `craig-interpolation`.

Pre-implementation audit for issue #8, in the pattern of `docs/fragments-audit.md`. Revision 2,
after review: four load-bearing corrections (countable generated `U`, the finite-support
invariant with `InsepAt`, the strengthened abstraction acceptance lemmas, dropping the witness
supply `T` in the relational core) and the nonempty entailment convention. The Zorn diagnosis
(Finding 1) stands. Sequencing is now kernel-first: the constant-support/abstraction mechanism
is built and gated BEFORE the Henkin interface.

## Post-implementation correction (coverage)

Coverage — "every ambient relation symbol belongs to side 1 or side 2" — was required by the
originally planned global invariant `GenU ⊆ Sent₁ ∪ Sent₂`. The implemented paired family
(`PairedInsepFamily.lean`) instead carries **coordinatewise** side bounds `Γ ⊆ SentBnd F₁ R₁`,
`Δ ⊆ SentBnd F₂ R₂` and proves their preservation **field-by-field**: every refinement rule keeps
the added sentence in the side of the trigger. Since no rule ever introduces an uncovered relation
atom (the seed's dormant atomic instances in `GenU` are never enumerated into `S*`), coverage is
unnecessary — the countable relational endpoint `craig_interpolation_relational_countable`
(`CraigRelational.lean`) has **no** coverage or side-bound hypothesis, only relation-symbol
countability. This is a positive simplification, not interface drift.

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
  transported back by `mapLanguage_restrictSymbols` + `realize_mapLanguage`
  (issue milestone 2). The countable core theorem carries the countability instances.

### D1 (frozen) — nonempty entailment

```
def Theoryω.Entails (T : L.Theoryω) (ψ : L.Sentenceω) : Prop :=
  ∀ (M : Type) [L.Structure M] [Nonempty M], T.Model M → Sentenceω.Realize ψ M

def Sentenceω.Entails (φ ψ : L.Sentenceω) : Prop := Theoryω.Entails {φ} ψ
```

- **Set-level entailment is the primitive** — the inseparability closure lemmas are about
  `Γ ⊨ σ` with Γ a set; the sentence form is the derived headline convention.
- **Carriers at `Type 0`**, matching the `ScottCompletion.lean` precedent and matching where
  the contradiction model lives; universe generalization is later cosmetics, not this arc.
- **`[Nonempty M]` is part of the convention** (standard model theory). This is forced, not
  cosmetic: the constant-elimination arguments expand a base `L`-structure by interpretations
  of the fresh constants, which is impossible over an empty carrier — so entailments produced
  through the fresh-constant machinery cannot be certified for empty base structures. An
  empty-carrier wrapper (via the symbol-free sentence `∃x x = x`) can be layered on later if
  ever wanted; the core convention is nonempty.

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
| realization transfer | `realize_mapLanguage` (Operations.lean:649, via `IsExpansionOn`), `expandSymbStructure` (MorleyHanfSchemaDischarge.lean:63 — should be MOVED to a Methods/ file when consumed here; `Conditional/` is the wrong home for a dependency of an unconditional headline) |

Additionally the **constant-support calculus** exists in prototype: MarkerStage.lean already
hit the finite-support problem (its Layer-5 header, `MarkerStage.lean:906` region: arbitrary
`L_ω₁ω` formulas have infinite constant support — `⋁ₙ (dₙ = dₙ)` mentions every constant — so
freshness needs a carried finite-support invariant, exactly as here), and its `sentenceJConsts`
+ monotonicity lemmas (`MarkerStage.lean:190–232`) are already generic in a single expansion
`L'[[J]]`. Its Layer-4 `realizeWith` congruence (`realizeWith_congr`) is the
constant-interpretation surgery engine, specialized to the double expansion. Kernel step 2
moves/generalizes this calculus into a neutral module for the single expansion `L[[J]]`.

## 4. The Marker/Keisler route mapped to the repository

Fix the occurrence pairs `F₁ = φ₁.functionsIn`, `R₁ = φ₁.relationsIn` (side 1), likewise
`F₂, R₂` (side 2), and `F₀ = F₁ ∩ F₂`, `R₀ = R₁ ∩ R₂` (shared). Work in `L[[ℕ]]` (after the
milestone-2 symbSublang reduction, over the countable joint sublanguage). Three DISTINCT roles,
kept separate:

- **Side/symbol predicates** `Sent₁, Sent₂, Sent₀`: sentences of `L[[ℕ]]` whose base symbols
  lie in the respective occurrence pair, **with finite constant support**. These are
  *unrestricted* predicates (each is a proper class-sized set of syntax — even over a countable
  language the type of `L_ω₁ω` sentences is uncountable: `ℕ → Formula` functions already give
  continuum many conjunctions). They classify pairs and separators; nothing enumerates them.
- **The countable enumeration domain `U`**: the *inductively generated* closure of the two
  root sentences `{φ₁', (φ₂').not}` under components, polarity operations, and constant
  instantiation (§8). `U` is countable by construction, every member has finite constant
  support (the generators do, and every operation preserves it — the MarkerStage Layer-5
  observation), and `U ⊆ Sent₁ ∪ Sent₂`. Only the Henkin construction runs through `U`.
  **Separators are NOT confined to `U`** — they live in `Sent₀` with support in the pair's
  allowed `Finset`.
- **Finite pairs**: the consistency-property members are `S = Γ ∪ Δ` with `Γ, Δ` FINITE
  (`Set.Finite`, or `Finset`-valued at the interface — decided in the next tranche), `Γ ⊆
  Sent₁ ∩ U`, `Δ ⊆ Sent₂ ∩ U`. Finiteness is what makes the allowed-support `Finset` exist
  and makes C7 freshness a triviality. The enumeration's stages are finite; only the limit
  `S*` is countably infinite, and the truth lemma consumes `S*` through `HenkinComplete`, not
  through membership in the property (Finding 1).

The route:

1. `InsepAt A Γ Δ` (§7): no separator with base symbols in `(F₀, R₀)` and **constant support
   inside the finite allowed set `A : Finset ℕ`**, entailed by Γ and refuted on Δ.
2. **Root gate (A = ∅)**: if φ₁ has no interpolant over `L`, then
   `InsepAt ∅ {φ₁'} {(φ₂').not}` — at `A = ∅` separators are automatically constant-free, and
   a constant-free separator strips to an `L`-interpolant (`stripConsts`, §6). No "upgrade
   over countably many constants" is needed anywhere; this was the point of parameterizing by
   `A`.
3. The inseparable finite pairs (each carrying `A` = the constants occurring in `Γ ∪ Δ`) form
   the fragment-relative consistency property on `U` (closure lemmas, §7); C7 steps
   temporarily pass to `insert c A` for a fresh `c` and the abstraction theorem transports
   separators back down to `A`.
4. Fragment-relative model existence (enumeration through `U`, §5–6) yields `M ⊨ φ₁ ∧ ¬φ₂`
   with `M` nonempty, contradicting `Sentenceω.Entails φ₁ φ₂`.

## 5. Field-by-field audit of `ConsistencyPropertyEq` — and the load-bearing finding

Verdicts against `Methods/Henkin/ConsistencyProperty.lean`, for the inseparability instance:

| Field | Quantification | Verdict |
|---|---|---|
| `C0_no_falsum`, `C0_no_contradiction` | members only (C0b's ∀φ is negative) | **fragment-safe as stated** |
| `C1`, `C1'`, `C2`, `C3`, `C3'`, `C4`, `C4'` | decompose members | **fragment-safe as stated** — components of a `U`-sentence stay in `U` |
| `extension` | **∀ φ : Sentenceω** | **BROKEN** (the issue's "hidden prerequisite"): mixed sentences with private symbols from both sides can be added to neither coordinate. And per D5 the forward-only truth lemma does not need it: dropped, not restricted. |
| `chain_closure` | arbitrary ⊆-chains | **FALSE for inseparability — see Finding 1.** Dropped, not restricted. |
| `C5_eq_refl`, `C7_all`, `C7_neg_ex`, `C7_all_bound`, `C7_neg_all_bound` | **∀ t : closed L-term** | **BROKEN** over a joint language with function symbols (mixed terms). In the **relational core** (§9) the only closed terms of `L[[ℕ]]` are the constants, all shared, so the fields are stated over closed terms verbatim and are fragment-safe. No witness-supply parameter `T` (correction 4): a designated `T` would need function-application closure to support a term-model structure, which is machinery the relational core doesn't need — the ordinary closed-term quotient works. If a generic `T` is ever wanted (it isn't, before relationalization), it must be packaged with `∀ f args, (∀ i, args i ∈ T) → Term.func f args ∈ T`. |
| `C6_eq_subst` | ∀ t₁ t₂ closed, ∀ φ : Formulaω (Fin 1) | **DO NOT retain as unrestricted C6** — a countable `U` cannot be closed under arbitrary one-variable substitution templates (continuum-many one-hole presentations; see §6b C6-correction). Replace with the atomic congruence API: equality refl/symm/trans + relation congruence under one-argument replacement. |
| `C7_quantifier`, `C7_neg_all` (∃-witness forms) | witness `∃ t` | safe in the relational core: witnesses are constants; the instance supplies FRESH constants (outside the pair's `A`), which the finite-support invariant makes available. |

### Finding 1 (load-bearing, CONFIRMED): `chain_closure` is false for inseparability, so the Zorn route is unusable

`L_ω₁ω` entailment is not compact, and separability of a union does not descend to a chain
stage. Concrete refutation, entirely inside a common vocabulary `{0, S, c}` (so it applies to
any fragment-relative generalization, not just an unlucky side-split):

- `Γₙ = { ¬(c = Sᵏ0) : k < n }`, `Δ = { ¬θ }` where `θ = ⋀ₖ ¬(c = Sᵏ0)`.
- Each `(Γₙ, Δ)` is inseparable: the structure `ℕ` with `c := n` models `Γₙ` and refutes θ,
  so no σ with `Γₙ ⊨ σ ⊨ θ` exists.
- The union pair `(⋃ₙ Γₙ, Δ)` is separated by `σ = θ` itself.

Consequently `ConsistencyProperty.exists_maximal` (Zorn over `chain_closure`,
`Construction.lean:63`) cannot be instantiated, and the existing pipeline
`exists_maximal → MaximalConsistent → truthLemma` is unavailable *as a pipeline*. The correct
construction is a countable **enumeration** (Henkin priority argument) through `U`; the limit
`S*` satisfies a completion predicate (`HenkinComplete`) because each pair of relevant members
cohabits some finite stage — never because `S*` is in the property. Refactor plan in §6b.

## 6. The two-tranche plan

### 6a. Tranche 1 — the constant-support/abstraction kernel — **COMPLETE + GATED**

The genuinely uncertain mechanism is syntax/freshness, so it is built and tested first, in
neutral modules with no interpolation-specific commitments beyond `InsepAt`. All landed
axiom-clean in the WIP target: `Lomega1omega/Entailment.lean`, `Methods/ConstantSupport.lean`,
`Methods/ConstantAbstraction.lean`, `Methods/Interpolation/{ConstantElimination, Inseparability}.lean`.
**Tranche 1.5** (post-review bridges) also landed: `Methods/Interpolation/QuantifierRoundTrip.lean`
(the substitution round-trip `genEx c (instConst c ψ) ≡ ψ.ex` + the arbitrary-syntax C7
consumers for `ψ.ex` and `(ψ.all).not`) and `Methods/Interpolation/RootGate.lean` (the semantic
root gate — an empty-support separator strips to a genuine base interpolant, via the
cross-language entailment bridge `entails_reduct_of_entails_map`).

1. **Entailment** (D1): `Theoryω.Entails` / `Sentenceω.Entails`, nonempty, `Type 0`; basic
   monotonicity/weakening lemmas.
2. **Constant-support calculus**, moved/generalized from MarkerStage into a neutral module,
   for the single expansion `L[[J]]`: `constsIn` (terms/formulas) with the monotonicity
   calculus (not, imp components, iInf/iSup components, all/ex, openBounds, subst),
   finiteness transport, base-symbol projections (`baseFunctionsIn`, `baseRelationsIn`), the
   instance-confined realization wrappers with constructor simps, the **constant-agreement
   congruence** (surgery engine), invariance of realization outside the updated support, and
   the bridge between an arbitrary `L[[J]].Structure` instance and its base+constants
   decomposition.
3. **`abstractConstant`**: constant withdrawal into a fresh FREE variable (`… α n → … (α ⊕
   Fin 1) n` — free variables don't shift under binders, so the recursion crosses `all`
   cleanly; the single leaf-level relabel shuffle is confined to atomic cases), with the
   realization engine lemma (evaluating the abstracted formula at `a` ≡ evaluating the
   original with the constant reinterpreted to `a`), the substitution round-trip, and
   **constant-support deletion** (`constsIn (abstract j φ) ⊆ constsIn φ \ {j}`, other
   occurrence sets preserved).
4. **The acceptance pair** (correction 3 — these, not `Γ ⊨ σ(c) ⇒ Γ ⊨ ∃xσ`, are the actual
   C7 consumers), under freshness of `c` outside Γ resp. Δ:

   ```
   Γ, φ(c) ⊨ σ(c)   ⟹   Γ, ∃x φ(x) ⊨ ∃x σ(x)          (c fresh for Γ, φ, σ-support tracked)
   Δ ⊨ ¬σ(c)        ⟹   Δ ⊨ ¬∃x σ(x)                    (c fresh for Δ)
   ```

   Both by reinterpretation of `c` (the congruence + engine lemma). Together they transport a
   separator from support `insert c A` back to support `A`.
5. **`InsepAt (A : Finset ℕ) Γ Δ`** + the separator abstraction theorem (C7 transport:
   `InsepAt A (Γ ∪ {∃xφ}) Δ → InsepAt (insert c A) (Γ ∪ {φ(c)}) Δ` for fresh `c`,
   contrapositive of the acceptance pair) + the **A = ∅ root gate** (constant-free separators
   strip to `L`-interpolants: `stripConsts` + `realize_mapLanguage` transfer + occurrence
   transport; needs `[Nonempty]` to expand base structures by constant interpretations —
   the reason D1 is nonempty).
6. **Toy C7 test**: the exact closure argument exercised end-to-end on a concrete pair
   (the #11-spike pattern), certifying the interfaces compose before the Henkin tranche
   commits to them.

### 6b. Tranche 2 — the Henkin interface (only after the tranche-1 gate)

Recommended five-step split (post-review):

1. **Generated universe.** Define `U` with explicit constructors for: root formulas and
   connective components; polarity targets; constant quantifier instances (`instConst`);
   **all constant equalities needed by reflexivity/symmetry/transitivity**; and **atomic
   relation instances with their one-coordinate replacements**. Prove countability, finite
   constant support, and preservation of side membership.
2. **Rule interfaces.** Define `ConsistencyPropertyEqOn U` and `HenkinComplete U S` using the
   **atomic equality/congruence fields** (§C6-correction below) and the forward two-polarity
   connective fields; add the `MaximalConsistent → HenkinComplete` compatibility bridge
   (existing `model_existence` endpoints untouched).
3. **Fair enumeration.** A countable request type, every request repeated infinitely often,
   every stage finite and in the consistency family, and the union proved `HenkinComplete`
   **without** claiming it belongs to the family (Finding 1).
4. **Inseparable-pair instance.** Members witness finite `Γ`, finite `Δ`, a finite support `A`,
   support containment, side membership, and `InsepAt F R A Γ Δ`. Prove the closure rules,
   using the tranche-1 C7 theorem (`insepAt_instConst_of_insepAt_ex`) for fresh witnesses.
5. **Relational term model.** Quotient ordinary closed terms, prove the forward positive/negative
   truth lemma, then model existence; then the endpoint chain (§9–10).

**C6 correction (load-bearing — do NOT retain unrestricted C6).** A countable `U` cannot be
closed under arbitrary one-variable substitution templates: one infinitary sentence with
countably many occurrences of `c₀` admits continuum-many one-hole presentations (choose
independently which occurrences came from the variable), so substituting `c₁` yields
continuum-many C6 conclusions. The relational term model consumes only **atomic** closure:
equality reflexivity, symmetry, transitivity, and **relation congruence under replacement of
one argument**. Use those atomic fields directly — they are countable and sufficient, and the
`MaximalConsistent` bridge derives them from its existing C5/C6. (A guarded C6 requiring the
target instance already in `U` is a fallback, but the atomic API is cleaner.)

## 7. The inseparability closure lemmas

`InsepAt (A : Finset ℕ) (Γ Δ : Set (L[[ℕ]].Sentenceω)) : Prop` — no σ with base symbols in
`(F₀, R₀)`, `constsIn σ ⊆ A`, `Γ ⊨ σ`, and `Δ ⊨ σ.not`. Normally `A` = the constants
occurring in `Γ ∪ Δ` (finite, since pairs are finite with finite-support members), but the
parameter is what makes the C7 step and the root gate compositional. One closure lemma per
interface field, each with the *separator-combination* content:

| Field | separator combination |
|---|---|
| C1/C1'/C2 dichotomies | `σ₁ ∨ σ₂` (side 1) / `σ₁ ∧ σ₂` (side 2) |
| C3, C4' (∀-shaped, per-k) | separator unchanged |
| C3', C4 (∃-shaped: some k) | `⋁ₖ σₖ` resp. `⋀ₖ σₖ` — **the essential `L_ω₁ω` step**: countably many per-disjunct separators recombine by a countable connective. All σₖ share the same finite allowed support `A` — this is what the finite-support invariant buys; without it the combined separator could have infinite constant support and the root gate would be unreachable. |
| C5 / atomic equality congruence | separator unchanged (equality steps happen within one side; constants are common-vocabulary) |
| C7 family | `∃x σ(x)` via the abstraction theorem: pass to `insert c A`, abstract the fresh `c` back out (§6a.4–5). Exposed for arbitrary existential / negated-universal parents by `insepAt_instConst_of_insepAt_ex` / `insepAt_not_instConst_of_insepAt_not_all` (tranche 1.5). |

**D4 — dualization.** `InsepAt` is symmetric under `(Γ, Δ) ↦ (Δ, Γ)` with `σ ↦ σ.not` (up to
a double-negation realize lemma). Freeze: prove each closure lemma for side 1 only and derive
side 2 through the swap lemma — halves the connective-by-connective work and keeps the side-2
statements from drifting.

`InsepAt`'s definition carries the occurrence bound (base symbols in `(F₀, R₀)`, constants in
`A`), so the headline's occurrence conclusions need no separate bookkeeping: occurrence sets are
transported only at the root gate (`A = ∅`, now `base_interpolant_of_empty_support_separator`)
and the symbSublang round-trip (milestone 2).

## 8. The countable enumeration domain `U` (tranche 2; frozen shape)

`U` is NOT `Sent₁ ∪ Sent₂` (uncountable — §4). It is the least set of `L[[ℕ]]`-sentences
containing `φ₁'` and `(φ₂').not` and closed under: components of members (imp/iInf/iSup
projections), the polarity operations the C-fields add (`.not` of components, double-negation
targets), and constant instantiation of members' quantifier bodies (`(φ.openBounds).subst
(fun _ => (L.con m).term)` and the negated forms, for all `m : ℕ`). Countability by the
`List`-path-encoding technique of `Fragment.generated_countable` in spirit (the #13 `Fragment`
structure itself is NOT the host: it deliberately excludes substitution closure —
`Fragment.lean:17` — and lives at `BoundedFormulaω Empty n` across arities). Finite constant
support: the roots are constant-free `mapLanguage`-images, every closure operation preserves
finite support (components/negations shrink it, instantiation adds one constant) — the
MarkerStage Layer-5 invariant argument verbatim. Side membership: `U ⊆ Sent₁ ∪ Sent₂` since
each operation stays within the member's own side.

## 9. Relationalization boundary

The core runs over relational `L₁, L₂` sides: after adjoining constants to a relational
language, every closed `L[[ℕ]]`-term is a constant, all common-vocabulary — so the term
fields hold verbatim, the term model is the ordinary closed-term quotient (= constants/∼),
and no witness-supply parameter exists (correction 4). Freeze: the core theorem is
`craig_interpolation_relational` at countable symbol sets; milestone 2 removes ambient
countability via symbSublang; **relationalization is a separate final layer** translating
function symbols to graph relations (a new, self-contained syntactic translation with a
realize bridge — not started until the relational core is stable). Note: the headline as
frozen in §2 (with `functionsIn` in the conclusion) is delivered only after this layer; the
intermediate relational endpoint is the arc's first publishable theorem and gets the
blueprint node.

### 9a. Relational endpoint — CONSOLIDATED (this milestone)

The relational core is stable and consolidated as a publishable result (no release cut yet —
the full theorem is the release boundary):

* Layer 1 `craig_interpolation_relational_countable` (`CraigRelational.lean`) — relational +
  countable relation symbols;
* neutral prerequisite `SymbSublangExpansion.lean` — `expandSymbStructureBase` + reduct/realize/
  entailment transport for the two-sorted `symbSublang`;
* Layer 2 `craig_interpolation_relational` (`CraigSublanguage.lean`) — relational, **no** ambient
  countability (pass to `symbSublang` of the roots' countable symbol sets, apply Layer 1, map
  back); blueprint node `thm:craig-relational`;
* PC-separation `craig_pcSeparation_relational` (`CraigSeparation.lean`, audit §10) — the
  shared-vocabulary `symbSublang` packaging consumed by #10;
* public facade `ModelTheory/CraigInterpolation.lean`, wired into `InfinitaryLogic.All`
  (`import InfinitaryLogic` exposes both theorems), axiom-clean.

### 9b. Relationalization design — FROZEN (standard graph construction)

The final layer (arbitrary language → relational core) uses the standard graph construction —
**not** the constants-only path, which dodges the real difficulty (finite auxiliary-variable
binding and nested terms) and would produce a throwaway API. The relationalized language keeps
base relations and function graphs disjoint *by construction*, which simplifies the occurrence
proofs:

```
inductive GraphRelation (L : Language) : ℕ → Type
  | base  : L.Relations n → GraphRelation L n
  | graph : L.Functions n → GraphRelation L (n + 1)
```

The relationalized language has **no** function symbols. Build in gated units:

1. **Graph language and structures** — the graph expansion of an `L`-structure; base/graph
   relation realization lemmas; occurrence projections back to the original relations/functions.
2. **Finite existential block** — a neutral helper binding a finite tuple of auxiliary variables,
   with its realization theorem (the real syntax prerequisite for arbitrary arities). A pilot, if
   wanted, is an **arbitrary-arity** nested-term `termGraph` theorem — never a zero-arity case.
3. **Term graph** — `termGraph t y` with the acceptance theorem
   `Realize (termGraph t y) ↔ (realize y = Term.realize t)` for arbitrary nested terms and
   arbitrary function arities.
4. **Formula translation** — equality/relation atoms flattened through term graphs; `imp`/`all`/
   `iInf`/`iSup` translated structurally; full realization bridge in graph expansions; exact
   occurrence bounds.
5. **Graph axioms** — for a countable set `F` of function symbols: totality; functionality; the
   countable conjunction `graphAxioms F`; reconstruction of an `L`-structure from a relational
   model of these axioms; realization bridge for formulas using only functions from `F`.
6. **Back-translation** — base relations unchanged; `graph f (x⃗,y) ↦ f(x⃗) = y`; structural
   through every connective; realization and occurrence theorems.
7. **Craig assembly** — apply relational interpolation to
   `Ax(F₁) ∧ r₁ʳᵉˡ ⊨ Ax(F₂) → r₂ʳᵉˡ`. The intersection of the two relational vocabularies is
   exactly {base relations shared by `(r₁,r₂)`} ∪ {graph relations for functions shared by
   `(r₁,r₂)`}, so back-translation gives the sharp function- and relation-occurrence bounds.

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
representation of "shared vocabulary" — consistent with the milestone-2 machinery; #10 can
re-package.

## 11. Decision points (all frozen at review)

| # | Decision | Frozen |
|---|---|---|
| D1 | entailment | set-level primitive, `Type 0` carriers, **`[Nonempty M]`** |
| D2 | universe scope | `Language.{0,0}` for the whole arc |
| D3 | pair representation | existential-pair form, **finite** coordinates, allowed-support `Finset` carried by `InsepAt`'s parameter |
| D4 | side-2 closure lemmas | via the `InsepAt`-swap lemma, not re-proved |
| D5 | `extension` field | dropped; forward-only two-polarity truth lemma |
| F1 | Zorn/`chain_closure` | unusable (refuted §5); fair enumeration through countable `U` |
| F2 | abstraction kernel | tranche 1, gated by the toy C7 test before any Henkin work |
| C1–C4 | review corrections | `U` = countable generated closure (not `Sent₁ ∪ Sent₂`); finite-support invariant + `InsepAt A` (root `A = ∅` replaces the root-pair upgrade); acceptance pair = fresh-constant elimination sequents; no witness supply `T` (relational core, ordinary closed-term quotient) |
