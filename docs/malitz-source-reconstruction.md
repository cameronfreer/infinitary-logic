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
`C*`-constant at all.**  The budget stays empty for the whole construction: every sentence added to
`S₂` is a substitution instance of a subformula of a member of `S₂`, so `Un(S₂)` never grows.

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

**Recommended order for Unit 3** (review): (1) canonical side projections; (2) the shared-overlap/C0
toy theorem; (3) the projection-aware left *and* right C7 identity theorems; (4) only then audit the
remaining consistency fields.

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
