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
constants `Cˢ = {cˢₙ}`, and let `C* = ⋃ₛ Cˢ`.  For a set `S` of sentences, `S₁` is the set of
`τ₁ ∪ C*`-sentences of `S` using only finitely many `C*`-constants, and `S₂` the `τ₂ ∪ C*`-ones.
Define

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

**There is none, because the flow is inverted.**  Our Craig engine grows a finite constant support
`A`, allows the separator to use it, and strips constants at the root (`A = ∅`, `stripConsts`).
Feferman's proof runs the other way: the root pair `{φ, ¬ψ}` is where the argument *starts*, it is
constant-free, so `Un′ = Un` and `Ex′ = Ex` there, and the theorem's clauses 2–3 are literally the
root instance of the separation relation.  The consistency property then propagates (⋆) **downward**
to a model, and the contradiction closes the proof.

So residue never has to be removed: the invariant is a hypothesis at the root, not a conclusion at
the end.  The answer to the frozen acceptance question is therefore:

> **Yes** — a certificate retains a shared core while carrying nonshared residue, the residue being
> the `C*`-constants, charged into both budgets.  And **the residue never has to disappear at the
> root, because the root is the starting point, not the terminus.**  In the single-sorted Malitz
> specialization the residue is moreover *never admitted at all*: the empty existential budget
> forbids constants in the separator outright.

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

## 6. Consequences for the repository

**Diagnosis of Unit 2, in these terms.**  Candidate 1 restricted the separator's class absolutely
and kept Craig's support parameter.  Feferman's certificate does the opposite: it restricts the
class *relative to the two sides' own quantifier content*, and prices the support into that
restriction.  Our left-C7 failure was not a missing lemma; it was the wrong certificate.

**Proposed candidate-3 certificate** (single-sorted, the only form #15 needs — to be frozen by
review before any Lean):

```
MalitzSepAt F R Γ Δ  :=  ¬ ∃ σ,  IsUniversal σ
                            ∧ σ.baseFunctionsIn ⊆ F ∧ σ.baseRelationsIn ⊆ R
                            ∧ sentenceJConsts σ = ∅          -- constant-free, NOT support-⊆ A
                            ∧ Theoryω.Entails Γ σ ∧ Theoryω.Entails Δ σ.not
```

Note what changed: the finite support parameter `A` **disappears**, replaced by outright
constant-freeness.  The audit's four Task-2 items are then answered as: certificate = a universal
constant-free separator; shared-symbol invariant = unchanged `(F₁ ∩ F₂, R₁ ∩ R₂)`; both C7
transformations = **the identity**; root-to-interpolant equation = trivial, the separator already is
the interpolant.

**The left-C7 toy theorem to compile first** (§D8 Task 3), now genuinely small:

```
theorem malitzSepAt_witness (c : ℕ) (φc : L[[ℕ]].Sentenceω)
    (hcΓ : ∀ γ ∈ Γ, c ∉ sentenceJConsts γ)
    (h : MalitzSepAt F R (insert (genEx c φc) Γ) Δ) :
    MalitzSepAt F R (insert φc Γ) Δ
```

— no support arithmetic, and the separator is transported unchanged; only the entailment moves, by
the reinterpretation argument already used in `entails_genEx_of_entails`.  The right-hand twin is
the same statement on `Δ`.

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
