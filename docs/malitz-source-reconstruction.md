# Malitz interpolation (#15): source reconstruction of the missing construction

Deliverable of the §D8 audit gate of `docs/malitz-audit.md`.  Its required content is **not** a
broad proof summary but two explicit items:

1. **the exact invariant maintained at the fresh-witness step**, and
2. **the mechanism that removes all nonshared residue at the root**.

Both are identified below.  The construction was found, and it is **not** a repair of the
paired-family invariant we tried in Unit 2 — it is a different certificate, and in the single-sorted
Malitz case it makes the fresh-constant machinery unnecessary altogether.

## 1. Sources

| source | status | what it gives |
| --- | --- | --- |
| Harrison-Trainor–Kretschmer, *Infinitary Logic Has No Expressive Efficiency Over Finitary Logic*, [arXiv 2209.05615](https://arxiv.org/pdf/2209.05615) §4.2.2 | **read** | statements and scopes of Theorems 4.5–4.7; confirms 4.6 is derived from 4.5; **no proofs** |
| Väänänen, *Interpolation in model theory*, [arXiv 2507.19097](https://arxiv.org/pdf/2507.19097) (25 Jul 2025), §on infinitary interpolation | **read** | Theorem 22 with its **consistency-property proof**, and Theorem 23 (= Malitz's preservation theorem) **derived from it** |
| Feferman, *Lectures on proof theory*, Leeds 1967, Springer LNM 70 (1968) 1–107 | **not read** | the original of Väänänen's Theorem 22 (cited there as [17]) |
| Malitz, *Universal classes in infinitary languages*, Duke Math. J. 36 (1969) 621–630 | **not read** | the original of Theorems 4.5/4.6 |
| Keisler, *Model Theory for Infinitary Logic* (1971) | **not read** | the relative (mod-`σ`) version of 4.6 |

HTK confirm the audit's statements verbatim and add nothing about method: Theorem 4.5 is quoted and
attributed, and "As a consequence of this, Malitz proves the following, which applies to any
signature `τ`" introduces 4.6.  Theorem 4.7's proof is an explicit sketch ("expands the signature by
introducing a new relation symbol for each finitary formula and applies Theorem 4.6").

**The construction comes from Väänänen's survey, not from HTK.**  It is Feferman's *many-sorted*
interpolation theorem, which specializes to Malitz interpolation.  What follows quotes the survey
where it is explicit and marks clearly where the argument is reconstructed.

## 2. The construction: many-sorted interpolation with sort-quantifier budgets

Notation (survey): `Un(φ)` = the sorts `s` such that a variable of sort `s` occurs **universally**
quantified in `φ`; `Ex(φ)` dually; both extended to sets of formulas.

> **Theorem 22 ([17] = Feferman).**  Suppose `φ ⊨ ψ`, where `φ` and `ψ` are sentences of `L_ω₁ω` in a
> **relational** vocabulary.  Then there is a sentence `θ` of `L_ω₁ω` such that
> 1. `φ ⊨ θ` and `θ ⊨ ψ`
> 2. `τ(θ) ⊆ τ(φ) ∩ τ(ψ)`
> 3. `Un(θ) ⊆ Un(φ)` and `Ex(θ) ⊆ Ex(ψ)`.

**Proof shape** (survey, condensed).  Assume no such `θ`.  Introduce, for each sort `s`, new
constants `Cˢ = {cˢₙ}`, and let `C* = ⋃ₛ Cˢ`.  Now the decisive structural point, which is **not** a
pair of independent theories:

> Given a set `S` of sentences, `S₁` consists of all `τ₁ ∪ C*`-sentences in `S` with only finitely
> many constants from `C*`, and `S₂` consists of all `τ₂ ∪ C*`-sentences in `S` with only finitely
> many constants from `C*`.

`S₁` and `S₂` are **canonical side-language projections of one finite set `S`**, and `Δ` consists of
the finite `S` with `S = S₁ ∪ S₂` satisfying (⋆).  A **shared**-vocabulary sentence therefore lies in
**both** projections.  §6 explains why that overlap is load-bearing and why an arbitrary pair
`(Γ, Δ)` is not a faithful substitute.  Define

> `θ` **separates** `S′` and `S″` iff
> 1. `S′ ⊨ θ`, 2. `S″ ⊨ ¬θ`, 3. `Un′(θ) ⊆ Un(S′)`, 4. `Ex′(θ) ⊆ Un(S″)`,
>
> where **`Un′(θ)` consists of the sorts `s ∈ Un(θ)` *and the sorts of the constants* `c ∈ C*`
> occurring in `θ`**, and `Ex′(θ)` likewise from `Ex(θ)`.

`Δ` := the finite sets `S = S₁ ∪ S₂` such that **(⋆)** no `L ∪ C*`-sentence separates `S₁` and `S₂`.
Then `{φ, ¬ψ} ∈ Δ` by assumption, `Δ` is shown to be a consistency property, so `{φ, ¬ψ}` has a
model — contradicting `φ ⊨ ψ`.

Two conventions to carry over, both already native to this repository:

* `Un`/`Ex` are **signed** (polarity-aware) counts: the consistency property's negation clause is
  `¬φ ∈ S ⟹ S ∪ {φ¬} ∈ S` with `φ¬` the NNF negation, so `¬∀x` counts as existential.  Our Unit-0
  `universalSigned` is exactly this primitive without an NNF datatype; the many-sorted version is
  its set-valued generalization, i.e. the same shape as #14's `relationsInSigned`.
* Clause 4 bounds the separator's **existential** sorts by `Un(S″)` — the **negation exchange**,
  since `Un({¬ψ}) = Ex(ψ)`.  This is #14's flipped-class discipline, not a typo.

## 3. §D8 item 1 — the invariant at the fresh-witness step

**The invariant is (⋆) with the primed budgets: a separator may mention Henkin constants, and each
constant's sort is charged into *both* the universal and the existential budget.**

That single convention is what makes the witness step work.  The survey states the step and calls it
"almost trivial":

> Consider `S ∈ Δ` and `∃xˢ φ(xˢ) ∈ S₁`.  Let `c₀ ∈ Cˢ` be such that `c₀` does not occur in `S`.  Now
> the sets `S₁ ∪ {φ(c₀)}` and `S₂` satisfy (⋆).

**Reconstruction of the omitted computation** (ours; to be checked against Feferman).  Suppose `θ`
separates `S₁ ∪ {φ(c₀)}` from `S₂`.

*Case `c₀` does not occur in `θ`.*  Then `θ` separates `S₁` from `S₂` directly: `S₁ ⊨ θ` follows from
`S₁ ∋ ∃xφ` and freshness (expand a model of `S₁` by `c₀ ↦` a witness), and clauses 2–4 are unchanged.

*Case `c₀` occurs in `θ`.*  Put `θ′ := ∃xˢ θ[c₀ := xˢ]`.  Then

* `S₁ ⊨ θ′` and `S₂ ⊨ ¬θ′`, both by the reinterpretation argument (freshness of `c₀` for `S₁`, `S₂`);
* `Un′(θ′) ⊆ Un′(θ) ⊆ Un(S₁)` — no universal quantifier is added and `θ′` has strictly fewer
  constants;
* `Ex′(θ′) ⊆ Ex(θ) ∪ {s} ∪ (sorts of θ′'s constants) ⊆ Ex′(θ) ⊆ Un(S₂)` — **because `c₀` has sort
  `s` and already occurs in `θ`, `s ∈ Ex′(θ)` before the quantifier is introduced.**

So the newly introduced `∃` is **paid for in advance** by the constant it replaces.  This is the
mechanism our Unit-2 predicate lacked: `MalitzInsepAt` imposed `IsUniversal σ` **absolutely**, with
no charge attached to the constants in `σ`'s support, so `genEx` had to be paid for out of nothing —
and `not_isUniversal_genEx` is precisely that unpaid bill.

### The single-sorted collapse — and it is favourable

Malitz interpolation is single-sorted, so `Un`, `Ex` are subsets of a one-element sort set and the
budgets degenerate.  At the root, `S₁ = {φ}` and `S₂ = {¬ψ}` with `ψ` universal, so

```
Un(S₂) = Un({¬ψ}) = Ex(ψ) = ∅        hence      Ex′(θ) = ∅
```

and `Ex′(θ) = ∅` says two things at once: **`θ` has no existential quantifier, and `θ` contains no
`C*`-constant at all.**

**Correction (Unit-3 step 4 testing).**  An earlier draft asserted that the budget "stays empty for
the whole construction, because every sentence added to `S₂` is a substitution instance of a
subformula of a member of `S₂`".  That is **false in the projection representation**: `S₂` is a
projection of the *shared* set `S`, so decomposing a member of `S₁` can put a **shared** component
into `S₂` as well, and if that component carries universal quantifiers it raises `Un(S₂)`.  The budget
is genuinely **dynamic**, and §6's constant-free specialization is correspondingly **not** closed under
every consistency rule — see the C1 finding there.

Consequently, in the Malitz case:

* the separator is **universal and constant-free at every stage**;
* both fresh-witness steps are the trivial case above — a separator of the extended pair *is* a
  separator of the original, with freshness used only for the entailment transfer and **no syntactic
  transformation of the separator at all**;
* the `∀`-instantiation step (`∀xφ ∈ S₂ ⟹ S₂ ∪ {φ(c)}`) is free, because `S₂ ⊨ φ(c)` already;
* `genEx`, `genAll`, and the whole constant-abstraction apparatus are **not used**.

## 4. §D8 item 2 — the residue-elimination mechanism at the root

**There is none, because the separator is never allowed support in the first place.**

Both arguments in fact start at the root and extend a consistency condition downward — that much is
common to Craig and to Feferman, and an earlier draft of this document overstated the contrast as an
"inverted flow".  The real difference is narrower and sharper:

* our Craig engine **permits budgeted separator support** `A`, grows it as witnesses are added, and
  relies on the empty root budget (`A = ∅`, `stripConsts`) to deliver a constant-free interpolant at
  the end;
* Feferman's separation relation **never permits separator support at all** in the case that matters
  here — the constant charge makes `Ex′(θ) = ∅` incompatible with any `C*`-constant in `θ` — so there
  is no support to discharge and no stripping phase.

The root pair `{φ, ¬ψ}` is constant-free, so `Un′ = Un` and `Ex′ = Ex` there, and clauses 2–3 of the
theorem are literally the root instance of the separation relation.  The answer to the frozen
acceptance question is therefore:

> **Yes** — in the many-sorted theorem a certificate retains a shared core while carrying nonshared
> residue, the residue being the `C*`-constants, charged into both budgets.  And there is **no
> residue-removal phase**: the charge is what pays for generalization, and the root instance is
> constant-free by construction.  In the single-sorted Malitz specialization the residue is moreover
> **never admitted at all** — the empty existential budget forbids constants in the separator
> outright, at every stage.

## 5. Theorem 22 ⟹ Theorem 4.5, and the route to 4.6

**Malitz interpolation is the single-sorted case of Theorem 22.**  Let `φ ⊨ ψ` over a relational
(= function-free, matching 4.5's scope) vocabulary with `ψ` universal.  Then `Ex(ψ) = ∅`, so clause 3
gives `Ex(θ) = ∅`, i.e. `θ` is universal; clause 2 is the shared-symbol condition; clause 1 is the
interpolation.  That is Theorem 4.5 exactly.  The `Un(θ) ⊆ Un(φ)` half is not needed for 4.5.

**Preservation is obtained by a two-sorted encoding**, which the survey carries out for the absolute
downward form (its Theorem 23, attributed to Malitz [Mal69]): write `φ` in sort 0 and a copy `φ′` in
sort 1 with `R` replaced by `R′`, let

```
EXT  :=  ∀x¹ ∃x⁰ (x⁰ = x¹)  ∧  ∀x¹∀y¹ (R′(x¹,y¹) ↔ R(x¹,y¹))
```

so that `({M₀,M₁}, R, R′) ⊨ EXT` iff `(M₁,R′) ⊆ (M₀,R)`; then `EXT ∧ ¬φ′ ⊨ ¬φ`, and Theorem 22
yields `θ` with only sort-0 symbols, existential because *no sort-0 variable is universally
quantified in `EXT ∧ ¬φ′`*, and `⊨ ¬φ ↔ θ`.

This is the same idea as §D4.5's relativization encoding — but applied to the **interpolation
theorem**, not to a bare Henkin family, and with **sorts** doing the work of the unary predicate `U`.
That is why D4.5 failed and this does not: the quantifier budget is carried by the sort, so the
encoding constrains the interpolant's quantifiers instead of merely constraining its vocabulary.

**Two limits on this half, recorded so it is not over-promised.**  Väänänen's Theorem 23 is the
**absolute** submodel/universal preservation theorem, *not* the relative mod-`σ` Theorem 4.6 — the
relative version is Keisler's and is still unread.  And the `EXT` encoding uses **cross-sort
equality** (`∀x¹∃x⁰(x⁰ = x¹)`, i.e. overlapping sorts), for which this repository has no
representation at all.  Preservation is therefore a **later gate**, after interpolation, and it needs
its own audit; nothing in §6 depends on it.

## 6. Consequences for the repository

**Diagnosis of Unit 2, in these terms.**  Candidate 1 restricted the separator's class absolutely
and kept Craig's support parameter.  Feferman's certificate does the opposite: it restricts the
class *relative to the two sides' own quantifier content*, and prices the support into that
restriction.  Our left-C7 failure was not a missing lemma; it was the wrong certificate.

**Proposed candidate-3 certificate** — the **single-set / canonical-projection** invariant, frozen by
review.  Faithfulness to Väänänen's `S₁`/`S₂` is not cosmetic: dropping a constant-free separator
class into the old *pair* shell **breaks C0**.  Witness, with `P` shared:

```
Γ = {P(c)}      Δ = {¬P(c)}
```

The union is inconsistent, yet there need be **no constant-free universal separator** of the pair —
any separator has to mention `c`.  In Feferman's representation both sentences are shared, so each
occurs in **both** canonical projections; each projection is then inconsistent, and the constant-free
universal `⊥` separates them.  That overlap is exactly how C0 survives constant-freeness.

```lean
def side (F : Set (Σ n, L.Functions n)) (R : Set (Σ n, L.Relations n))
    (S : Set L[[ℕ]].Sentenceω) : Set L[[ℕ]].Sentenceω := S ∩ SentBnd F R

def FefermanInsep (F₁ R₁ F₂ R₂ …) (S : Set L[[ℕ]].Sentenceω) : Prop :=
  ¬ ∃ σ, IsUniversal σ ∧ σ ∈ SentBnd (F₁ ∩ F₂) (R₁ ∩ R₂) ∧ sentenceJConsts σ = ∅ ∧
      Theoryω.Entails (side F₁ R₁ S) σ ∧ Theoryω.Entails (side F₂ R₂ S) σ.not

def FefermanMem … (S) : Prop :=
  S.Finite ∧ S ⊆ GenU … ∧ S = side F₁ R₁ S ∪ side F₂ R₂ S ∧ FefermanInsep … S
```

Equivalently: a pair representation is admissible only if it **enforces that every shared sentence
occurs in both coordinates**, not merely in their union.  The support parameter `A` disappears
entirely, replaced by `sentenceJConsts σ = ∅`.

The audit's four Task-2 items are answered as: certificate = a constant-free universal separator of
the two canonical projections; shared-symbol invariant = unchanged `(F₁ ∩ F₂, R₁ ∩ R₂)`; both C7
transformations = **the identity on the separator**; root-to-interpolant equation = trivial, the
separator already *is* the interpolant.

**The C7 toy gates (§D8 Task 3), stated through the projections.**  Not "extend `Γ`" — extend `S`,
and let the projections fall out:

```lean
theorem fefermanInsep_witness (c : ℕ) (φc : L[[ℕ]].Sentenceω)
    (hpar : genEx c φc ∈ S) (hcS : ∀ γ ∈ S, c ∉ sentenceJConsts γ)
    (h : FefermanInsep … S) : FefermanInsep … (insert φc S)
```

If the witness instance is shared it enters **both** sides — but then its existential parent is
shared too (`genEx` does not add base symbols), so *both* entailment transfers can remove the fresh
constant with the separator unchanged.  The single load-bearing lemma is the constant-free freshness
transfer

```lean
theorem entails_of_entails_insert_witness (hpar : genEx c φc ∈ T)
    (hcT : ∀ γ ∈ T, c ∉ sentenceJConsts γ) (hcσ : sentenceJConsts σ = ∅)
    (h : Theoryω.Entails (insert φc T) σ) : Theoryω.Entails T σ
```

which is `entails_genEx_of_entails`'s reinterpretation argument with the conclusion left alone
instead of generalized — the separator's constant-freeness is what lets it be pulled back unchanged.

**A deliberate weakening from Feferman, recorded.**  His separation relation tracks the sort budgets
`Un′`/`Ex′` and *permits* `C*`-constants in the separator, charged into both.  `FefermanInsep` asks
only for a **constant-free universal** separator.  That is exactly sufficient for Malitz 4.5 — for
universal `ψ` the budget collapses to precisely this condition — but it is the **single-sorted,
theorem-oriented specialization, not Feferman's invariant verbatim**.  Any many-sorted use, the
preservation route included, must reinstate the budgets.

**The four pre-assembly gates (review), and their outcomes.**

1. **Coverage restored.**  `Covered F₁ R₁ F₂ R₂ S := S ⊆ side F₁ R₁ S ∪ side F₂ R₂ S`, with
   `covered_iff_eq` (the `⊇` half is automatic), `covered_of_forall_mem_sentBnd` — coverage *is* a
   joint-language condition — and `covered_insert`.  It does **not** come for free as in the paired
   construction.  Recorded caveat: `GenU` seeds *all* ambient relation atoms, so an ambient symbol in
   neither side breaks coverage; the joint `symbSublang` wrapper is what discharges it later.
2. **C0 generalized, two-sided.**  `not_fefermanInsep_of_contradiction` derives the kernel's
   `no_contradiction` from coverage alone: left projection inconsistent ⟹ separator `⊥`; right
   ⟹ separator `⊤`.  A third case — the contradiction split across the two projections — **cannot
   occur**, because `SentBnd` membership is negation-invariant (`mem_side_not_iff`), so `σ` and `σ.not`
   always lie in exactly the same projections.  The earlier shared-only lemma is retained but is
   superseded for discharging the field.
3. **The genuine `neg_all_witness` consumer, proved directly.**  The field starts from `(φ.all).not ∈ S`
   and inserts `(instConst c φ).not`.  Routing through a semantic congruence is *not* available here:
   such a step would have to move **projection membership** as well as truth, and `SentBnd` is not
   invariant under semantic equivalence.  So `entails_of_entails_insert_negInstConst` produces the
   witness directly from `¬∀x φ` and pulls the constant-free separator back unchanged, and
   `fefermanInsep_insert_negInstConst` is the gate.  Its two `hb` hypotheses are exactly the
   projection-membership obligations; they are **discharged unconditionally in the relational scope**
   (`…_of_isRelational`, using `baseRelationsIn_instConst` — an equality, newly extracted — and the
   emptiness of base function symbols), which is #15's frozen scope for interpolation (§D6).  In
   general they need `baseFunctionsIn (all φ) ⊆ baseFunctionsIn (instConst c φ)`, which the repository
   has only in the `⊆` direction: a recorded residual, not on the relational path.
4. **The weakening is documented** — item above, and in the module docstring.

**C1 finding — the strengthened invariant is not closed under implication branching.**  Tested first,
as review directed, and it fails exactly where projection *leakage* occurs.

*No leakage* (the branch sentences fit only the side already holding the implication): C1 goes through
in both orientations, with separators `τ₁ ∨ τ₂` and `τ₁ ∧ τ₂`, universal by the signed recursion,
constant-free and shared.  Landed as `fefermanInsep_imp_dichotomy_left` / `_right`.

*Leakage.*  Take `φ.imp ψ ∈ side₁ S` with `φ` **shared**, so `φ` also enters `side₂`, and `ψ` outside
the second side.  Then

```
side₁ S ∪ {φ.not} ⊨ τ₁      side₂ S ∪ {φ.not} ⊨ ¬τ₁
side₁ S ∪ {ψ}     ⊨ τ₂      side₂ S           ⊨ ¬τ₂
```

`τ₁ ∨ τ₂` no longer separates: `side₂ S ⊨ ¬τ₁` is unavailable — only `side₂ S ⊨ φ ∨ ¬τ₁`.  The
separator that *does* work is

```
(φ.not.imp τ₁).and (φ.imp τ₂)
```

legally **shared**, since `φ` is shared exactly in the leakage case, but in general **neither universal
nor constant-free**, `φ` being an arbitrary member of `S`.

**Diagnosis.**  This is precisely the gap review flagged: `FefermanInsep` is *stronger* than Feferman's
dynamic invariant, and the source does not claim the stronger form is closed under the rules.  What
pays for the leakage separator is the dynamic budget — the leaked `φ` enters `S₂`, raising `Un(S₂)`,
which licenses exactly the quantifiers and constants `(φ.not.imp τ₁).and (φ.imp τ₂)` needs.  So the
constant-free specialization is a **root-level reading of the conclusion, not an invariant**: the
`Un′`/`Ex′` budgets have to be carried through the construction, and only at the root does
`Ex(ψ) = ∅` collapse them to "universal and constant-free".

**Consequence for step 4.**  Bulk assembly on `FefermanInsep` is *not* viable.  The next design step is
to reinstate the budgets — in the single-sorted setting, two Booleans per projection tracking whether
the separator may quantify universally / existentially, with constants charged into both, so that
`sentenceJConsts σ = ∅` becomes a *derived* root fact rather than a standing hypothesis.  The three
landed C7 gates and the two no-leakage dichotomies port to that predicate unchanged in shape, since
none of them touches the budget; C0 and coverage are budget-independent already.

## 6a. The budgeted redesign, and where it stops

`FefermanInsep` is **retired as the stage invariant** (kept as the root-facing specialization and a
regression test).  The invariant carries Feferman's **two permissions**, not two per projection:

* a **universal** occurrence in the separator is licensed by a universal occurrence in the **left**
  projection;
* an **existential** occurrence is licensed by a universal occurrence in the **right** projection;
* any Henkin constant is charged to **both**.

This is `Un′(θ) ⊆ Un(S₁)`, `Ex′(θ) ⊆ Un(S₂)` read at one sort.

**Gate 1 — landed.**  `Lomega1omega/QuantifierOccurrence.lean`: a direct signed *occurrence*
recursion `hasQuantSigned`, with exact constructor equations (including `not`, `and`, `or`, `ex`,
`⊤`) and the exact bridge `universalSigned s φ ↔ ¬ hasQuantSigned (!s) φ`, hence
`IsUniversal φ ↔ ¬ HasExistential φ` and `IsExistential φ ↔ ¬ HasUniversal φ`.  Set-level versions
carry the budget sources, with the **non-growth** lemma `hasQuantSigned_insert_of_le` that every
branch step needs.

**Gate 2 — landed.**  `FefermanAllowed S₁ S₂ θ` exactly as specified, and `BudgetedInsep`.  Two
consequences worth naming: `isUniversal_and_constantFree_of_allowed` — when the right projection has
no universal occurrence, an allowed separator is universal **and** constant-free, which is the root
collapse the interpolant needs — and `fefermanAllowed_of_isUniversal`, its converse feed.  The
no-leakage C1 dichotomy ports unchanged in shape (`budgetedInsep_imp_dichotomy_left`), with the branch
budgets discharged by non-growth: `hasQuantSigned true (φ.imp ψ)` covers both `hasQuantSigned false φ`
and `hasQuantSigned true ψ`, so neither branch enlarges the left budget.

**Gate 3 — designed, deferred.**  With canonical projections `{r₁, r₂.not}` need not project to the
two singletons: a shared-vocabulary `r₁` also enters the right projection, which both enlarges the
right budget and blocks `side₂ ⊨ θ.not` from yielding `θ ⊨ r₂`.  The repair is two fresh nullary
relation tags, `rL := r₁ ∧ (Pₗ → Pₗ)` and `rR := r₂.not ∧ (Pᵣ → Pᵣ)`, with the left vocabulary the
base symbols plus `Pₗ` and the right plus `Pᵣ`: the initial projections are then exactly `{rL}` and
`{rR}`, their vocabulary intersection is exactly the original shared vocabulary, the tags add no
quantifiers and no constants, the right root budget is empty when `r₂` is universal, and semantic
untagging returns the interpolant.  **This is the final correction to the withdrawn "no root residue"
claim: canonical-projection overlap does create root residue unless the roots are tagged.**  It is
deferred only because it needs a language expansion by two nullary relations, which the repository
does not have.

**Gate 4 — attempted; the obstruction is *not* budget bookkeeping.**  Take the leaking C1 case again:
`φ.imp ψ ∈ side₁ S` with `φ` shared and `ψ` outside the right vocabulary.  The budgets behave exactly
as designed — the left budget does not grow, and the right budget grows by `HasExistential φ` in the
`φ.not` branch, which is the dynamic licensing at work.  But every separator that works semantically
must **case-split on `φ`**, and `φ` then occurs at *both* signs:

```
HasUniversal ((φ.not.imp τ₁).and (φ.imp τ₂))
  ↔ HasUniversal φ ∨ HasUniversal τ₁ ∨ HasExistential φ ∨ HasUniversal τ₂
```

`HasExistential φ`, `HasUniversal τ₁`, `HasUniversal τ₂` are all licensed on the left.
**`HasUniversal φ` is not**: `φ.imp ψ ∈ side₁ S` licenses only `HasExistential φ`, because the
antecedent position flips the sign.  The alternative separator
`(φ.not.and τ₁).or (φ.and τ₂)` has the same universal-occurrence set, and the obstruction is not an
artifact of the `imp` presentation: for the survey's own `⋁` rule the combined separator
`⋁ₙ (φₙ ∧ θₙ)` needs `HasExistential φₙ → Un(S₂)`, which is likewise unlicensed.

So, uniformly across the branching rules: **the separator must mention the leaked component, and the
leaked component's own quantifier content is licensed by neither budget.**  Nor does enlarging the
budget sources to the signed-subformula closure of the members help — the offending occurrence sits at
the *opposite* sign from the parent, so the closure does not contain it either.

Gate 3 does not change this: tagging fixes the root projections, while the obstruction appears at the
first branching step on a shared subformula.

**Consequence.**  The single highest-value unread item is now **Feferman [17] itself** (*Lectures on
proof theory*, Springer LNM 70, 1968, 1–107): two independent separator constructions fail at the same
point, and Väänänen's presentation omits exactly this step ("most are almost trivial").  Either
Feferman's branching separator differs from both candidates, or the family carries a further condition
that keeps shared components out of the other projection.  Gate 5 (porting the remaining fields) should
not start until that is known.

**Field-audit order (review, for step 4).**  Family shell, finiteness, universe membership and
projection coverage; C0 via the `⊥`/`⊤` two-side split; finite and countable branching, especially the
implication dichotomy; `all_inst` and the negated-universal witness gate; equality and relation
congruence; only then package `ConsistencyPropertyEqOn`.

The implication separator looks unproblematic: if both branch separators are universal then
`(σ₁.not).imp σ₂` is universal by the signed recursion (`isUniversal_imp` plus `isUniversal_not`), and
constant-freeness and shared vocabulary are both preserved by `.not`/`.imp`.  Countable conjunctions
and disjunctions do not change the quantifier class (`universalSigned_iInf`/`_iSup`).

**Reusable from Units 0–2**: `universalSigned` (Unit 0) is the right primitive and generalizes to
the sorted `Un`/`Ex`; `realize_of_embedding_signed` (Unit 1) is what the two-sorted `EXT` encoding
will consume.  `ConstantGeneralization.lean` is **not** consumed by this route — `genAll` was built
for a certificate this reconstruction discards.  It stays as neutral infrastructure for #16.

## 7. What is verified, and what is not

* **Quoted, not reconstructed**: Theorem 22's statement, the separation relation with the primed
  budgets, the consistency-property conditions, the witness-step assertion, Theorem 23 and its `EXT`
  encoding, and HTK's Theorems 4.5–4.7 with their attributions.
* **Reconstructed by us**: the budget computation for the witness step (§3), the single-sorted
  collapse to constant-free separators (§3), the derivation of Theorem 4.5 from Theorem 22 (§5), and
  the certificate proposal (§6).  The first two are the load-bearing ones.
* **Open verification**: Feferman [17] itself, for the witness-step computation and for whether the
  primed-budget convention is stated as we reconstruct it; and Malitz [Mal69]/Keisler [Kei71], which
  may use a different proof entirely — the §D8 abandonment clause is *not* triggered, since the
  construction found is a consistency-property argument of exactly the shape our machinery supports.
* **Not established**: that the remaining consistency-property conditions (C0–C6, equality, and the
  repository's sixteen `ConsistencyPropertyEqOn` fields) survive the constant-freeness restriction.
  That is the next gate after the toy theorem, not before it.
