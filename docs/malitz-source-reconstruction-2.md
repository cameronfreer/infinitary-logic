# Malitz interpolation (#15): second source reconstruction — Feferman's Theorem 4.3

Deliverable of the frozen charter in `docs/malitz-source-reconstruction.md` §6b.  Answers the five
questions, with a rule table.  **No Lean was written for this document.**

## 0. What was and was not obtained

| source | status |
| --- | --- |
| Feferman, *Lectures on proof theory*, LNM 70 (1968), Thm 4.3, pp. 55–62 | **paywalled, not read** (Springer redirects to authentication) |
| Feferman, *"Ah, Chu!"*, pp. 2–3 ([PDF](https://festschriften.illc.uva.nl/j50/contribs/feferman/feferman.pdf)) | **read**; contains Feferman's own statement of the theorem, its definitions "from [F1], p. 55", and his description of the proof mechanism |
| van der Giessen, *Interpolation through the Lens of Proof Theory* (ANU 2024), §3.2 ([PDF](https://comp.anu.edu.au/lss/lectures/2024/Logic@ANU_interpolation_lecture_notes.pdf)) | **read**; the split-sequent (Maehara) invariant and rule cases, propositional only |
| Stern, *A new look at the interpolation problem*, JSL 40 (1975) 1–13 | **paywalled, not read** |
| Väänänen, *Interpolation in model theory* | read previously |

So the architecture question is answered from **Feferman's own description of his proof** plus the
**standard split-sequent method** he is describing; his §4 text itself remains unread.  Every claim
below is marked accordingly.

## 1. Feferman's statement, in his own words

From *"Ah, Chu!"* pp. 2–3, repeating "some syntactic definitions from [F1], p. 55" for a relational
many-sorted language with equality and a partition `Sort₀`, `Sort₁` of the sorts:

> (iv) `Unᵢ(ϕ)` is the set of `s ∈ Sortᵢ` such that there is at least one **essentially universal
> occurrence** in `ϕ` of some variable of sort `s`.
> (v) `Exᵢ(ϕ)` is the set of `s ∈ Sortᵢ` such that there is at least one essentially [existential]
> occurrence in `ϕ` of some variable `u` of sort `s`.

*(The note repeats "universal" in (v); from the use in Theorem 3 it must read "existential".)*

> **Theorem 3.**  Suppose `ϕ` and `ψ` are formulas of `L*` and that `ϕ → ψ` is valid … Then there is
> an interpolant `θ` for `ϕ → ψ` in `L*`, such that:
> (i) `Rel(θ) ⊆ Rel(ϕ) ∩ Rel(ψ)`  (ii) `Sort(θ) ⊆ Sort(ϕ) ∩ Sort(ψ)`
> (iii) `Free₀(θ) ⊆ Free₀(ϕ) ∩ Free₀(ψ)`
> (iv) `Un₀(θ) ⊆ Un₀(ϕ)` and `Ex₀(θ) ⊆ Ex₀(ψ)`
> (v) `Ex₁(θ) ⊆ Ex₁(ϕ)` and `Un₁(θ) ⊆ Un₁(ψ)`.

> For the case that `Sort₁ = ∅` this follows from **Theorem 4.3 of [F1], p. 56, where it was
> established by a proof-theoretical argument**.  The theorem in full follows from Theorem 2-1 of
> Stern [S], p. 4, where it was established by a **model-theoretic forcing argument**.  (His statement
> also includes conditions on positive and negative occurrences of relation symbols, as in Lyndon's
> well-known interpolation theorem …)

Two cross-checks worth recording.  Feferman's (iv) `Ex₀(θ) ⊆ Ex₀(ψ)` **agrees** with Väänänen's
clause `Ex′(θ) ⊆ Un(S″)`, since `S″ = {¬ψ}` and `Un(¬ψ) = Ex(ψ)`.  And Feferman notes that where he
uses free variables, "**Stern … in place of additional constant symbols**" — i.e. Stern's version is
the *constant-based* one.

## 2. The five questions

### Q1 — the exact sequent invariant

**Answer: a split (partitioned) sequent, not a canonical projection.**  The standard form, verified
from the ANU notes §3.2:

> Let `Γ, Γ′, Δ, Δ′` be cedents and `θ` a formula such that `Voc(θ) ⊆ Voc(Γ, Δ) ∩ Voc(Γ′, Δ′)`,
> `⊢ Γ ⇒ Δ, θ`, and `⊢ θ, Γ′ ⇒ Δ′`.  We write this `⊢ Γ; Γ′ —θ→ Δ; Δ′` and call `Γ; Γ′ ⇒ Δ; Δ′` a
> **split sequent**.

Feferman's Theorem 4.3 is this invariant with three further clauses carried along the derivation:
the relation-symbol condition (i), the **free-variable** condition (iii), and the sort-quantifier
conditions (iv)–(v).  *(Verified: the split-sequent form and Feferman's clauses.  Not verified: that
his §4 uses exactly this presentation of the calculus.)*

### Q2 — the parent interpolant in the branching rule

**Answer: disjunction when the principal formula is on the left part, conjunction on the right.**
Verified verbatim for `∨l` (ANU §3.2), with the principal formula in the *left* part `Γ`:

> By applying induction hypothesis on `π₁` and `π₂`, we have `φ, Γ; Γ′ —θ₁→ Δ; Δ′` and
> `ψ, Γ; Γ′ —θ₂→ Δ; Δ′` … We claim that **`θ = θ₁ ∨ θ₂`**.

and the vocabulary computation is the distribution
`(Voc(φ,Γ,Δ) ∪ Voc(ψ,Γ,Δ)) ∩ Voc(Γ′,Δ′) = Voc(φ ∨ ψ, Γ, Δ) ∩ Voc(Γ′,Δ′)`.  Dually, principal on the
right part gives `θ = θ₁ ∧ θ₂`.

**This is exactly what we already proved.**  `budgetedInsep_imp_dichotomy_left` uses `τ₁ ∨ τ₂` and
`fefermanInsep_imp_dichotomy_right` uses `τ₁ ∧ τ₂`.  The two landed no-leakage theorems *are* the
source's rules; what was wrong was the surrounding representation, not the rule.

### Q3 — duplication, or retention on the derivational side?

**Answer: retained on their derivational side.  No duplication, hence no leakage.**  The ANU
presentation is explicit that the partition is *chosen*: "Note that the split in the conclusion is
fixed, but that we have chosen appropriate splits in the premisses."  Each formula belongs to exactly
one part; nothing is reprojected by vocabulary.  The `→l` case even *swaps* which part a premise's
formulas sit in, which is only meaningful for labelled sides.

This settles the frozen dichotomy: **the invariant is side-labelled**, and Väänänen's
canonical-projection framing is not Feferman's.  It also explains the survey's one-sided witness
update — operationally it behaves like labelled sides, as predicted.

### Q4 — how constants / free variables are charged

**Answer: they are not "charged into" the budgets — the free-variable condition is *primary* and the
quantifier conditions are its *consequence*.**  Feferman, verbatim:

> The point there is that in building up an interpolant following a **cut-free derivation** of
> `ϕ → ψ`, we are **forced to introduce quantifiers into the interpolant only as required to maintain
> the condition (iii)**, and that turns out to **lead to (iv)**.  Since no condition is imposed on free
> variables of `Sort₁`, we are forced to introduce quantifiers applied to those variables into the
> interpolant only as required in (v).

So the dependency runs `(iii) ⟹ (iv)`: an eigenvariable/constant that is not shared between the two
parts **must** be quantified out of the interpolant, and the sign of the quantifier introduced is what
puts a sort into `Un₀(θ)` or `Ex₀(θ)`.  Our `FefermanAllowed` had this **backwards** — its third
clause charges a constant into both permissions as a standing requirement, whereas the source derives
the permissions from the constant condition.

### Q5 — is there a semantic dual?

**Answer: yes, and it is the more repository-compatible one.**  Stern's Theorem 2-1 (JSL 40 (1975)
1–13, p. 4) proves the *full* theorem — both sort-parts, plus Lyndon-style positive/negative relation
conditions — by a **model-theoretic forcing argument**, and formulates it with **additional constant
symbols** rather than free variables.  Feferman's Sort₀ is Stern's `I^∧` and Sort₁ his `I^∨`.  A third
route exists: Otto's reformulation "using **relativized quantifiers in a single-sorted language** in
place of many-sorted languages; his proof is model-theoretic using **back-and-forth** systems"
(unpublished Stanford notes, 1998).

Väänänen's consistency-property presentation should therefore be read as an informal compression, and
its canonical-projection framing as a presentational choice that does not survive contact with the
rules.

## 3. Rule table

Rows marked **V** are verified verbatim; rows marked **D** are the duals obtained by exchanging the
two parts; the quantifier rows marked **F** state Feferman's principle rather than his rule text,
which was not obtainable.

| source rule | child interpolant(s) | parent interpolant | side assignment | Un/Ex calculation |
| --- | --- | --- | --- | --- |
| axiom, principal in the **right** part | — | `⊤` | fixed | none (V) |
| axiom, principal in the **left** part | — | `⊥` | fixed | none (D) |
| `∨l`, principal in **left** part | `θ₁`, `θ₂` | **`θ₁ ∨ θ₂`** | premises keep the conclusion's split | `Un/Ex(θ) = Un/Ex(θ₁) ∪ Un/Ex(θ₂)` (V) |
| `∨l`, principal in **right** part | `θ₁`, `θ₂` | **`θ₁ ∧ θ₂`** | as above | union, as above (D) |
| `→l`, principal in **left** part | `θ₁`, `θ₂` | `θ₁ → θ₂` | left premise **swaps** the two parts | union (V) |
| `∧r`, `→r`, `¬` | — | dual of the above | — | union (D) |
| `∀r` / `∃l` (eigenvariable `a`), principal in **left** part | `θ₁` | `∃a θ₁` if `a ∉ Free(right part)`, else `θ₁` | `a` is fresh for the whole sequent | the introduced `∃` puts `a`'s sort into `Ex₀(θ)` (F) |
| `∀r` / `∃l`, principal in **right** part | `θ₁` | `∀a θ₁` under the same condition | as above | the introduced `∀` puts `a`'s sort into `Un₀(θ)` (F) |
| `∀l` / `∃r` (instantiation) | `θ₁` | `θ₁` unchanged | term stays on its part | no new occurrence (F) |

**The decisive row** — `∨l` — is verified, and it matches the two dichotomy theorems already in the
repository.  The quantifier rows are exactly Feferman's "introduce quantifiers only as required to
maintain (iii)": a quantifier appears in the interpolant **iff** an eigenvariable would otherwise
escape the shared free-variable set, and its sign is determined by which part the rule fired on.

## 4. Verdict and consequences

The **predetermined outcome "formulas remain side-labelled" is selected.**

1. **Restart from a budgeted labelled-pair certificate**, `BudgetedPairInsep Γ Δ`, and **retire
   canonical `FefermanMem`** together with `side`, `Covered`, and the coverage machinery.
2. **The nullary-tag plan (gate 3) is cancelled**, not merely deferred: with labelled sides the root
   split is exact by construction, so there is no root overlap to repair.
3. **`FefermanAllowed` survives, with one correction**: its third clause must be *derived*, not
   assumed.  The primary invariant is the shared-constant condition `Free₀(θ) ⊆ Free₀(Γ) ∩ Free₀(Δ)`;
   the two quantifier permissions are what the forced quantifier-introduction produces.  The
   single-sorted reading of (iv) is precisely our two permissions —
   `Un₀(θ) ⊆ Un₀(left)`, `Ex₀(θ) ⊆ Ex₀(right)`.
4. **The landed no-leakage dichotomies are the real rules**, not a special case; and the failed
   universal-only C1 theorem retains its evidential role, now with a source-level explanation:
   the leakage it exposed is an artifact of canonical projection, which Feferman does not use.
5. **The old pair representation was never the error.**  Its universal-only separator restriction
   was, and that was retired in §6a.
6. `QuantifierOccurrence.lean` is unaffected and is exactly the `Un`/`Ex` calculus the clauses need.

**Gate order for the restart** (unchanged in spirit from the frozen plan): prototype
`BudgetedPairInsep`, then C1, then both C7 directions, then the root equation — and only then any
other field.

## 5. The restart, as landed

`Methods/Interpolation/BudgetedPair.lean`.  Per review, the old `FefermanAllowed` constant clause is
**not** retained as a stage assumption; the shared-constant condition is primary and the two
permissions are separate:

```lean
BudgetedPairSeparates F₁ R₁ F₂ R₂ Γ Δ θ :=
  Theoryω.Entails Γ θ ∧ Theoryω.Entails Δ θ.not ∧
  θ ∈ SentBnd (F₁ ∩ F₂) (R₁ ∩ R₂) ∧
  sentenceJConsts θ ⊆ theoryJConsts Γ ∩ theoryJConsts Δ ∧
  (hasQuantSigned true  θ → Theoryω.HasQuantSigned true Γ) ∧
  (hasQuantSigned false θ → Theoryω.HasQuantSigned true Δ)
```

| gate | declaration | outcome |
| --- | --- | --- |
| certificate | `BudgetedPairSeparates`, `BudgetedPairInsep` | landed |
| constant calculus | `theoryJConsts` + `_insert`, `_insert_of_subset`, `_mono`, `notMem_theoryJConsts_iff` | landed |
| C1 left / right | `budgetedPairInsep_imp_left` (`τ₁ ∨ τ₂`) / `_right` (`τ₁ ∧ τ₂`) | landed |
| fresh witness left / right | `budgetedPairInsep_witness_left` / `_right` | landed, **separator transported unchanged** |
| root collapse | `isUniversal_of_budgetedPairSeparates`, `sentenceJConsts_eq_empty_of_…` | landed |
| root equation | `exists_universal_interpolant_of_not_budgetedPairInsep` | landed |
| mixed C0 | `not_budgetedPairInsep_of_mixed` | landed, `σ` itself is the separator |

The witness rules use `entails_of_entails_insert_negInstConst_of_fresh`, which needs only
`c ∉ sentenceJConsts θ` — supplied by opposite-side freshness through the shared-constant condition.
No `genEx`, `genAll`, support parameter, projection coverage, or root tag appears anywhere in the
file, and a `run_cmd` cone probe confirms neither `FefermanProjection` nor `MalitzC7Spike` is in its
import cone.

**Remaining source leads, in priority order.**  (a) Stern's JSL paper — the model-theoretic forcing
version *with constants*, closest to this repository, and the one that also carries the Lyndon
conditions (relevant to #14's finished polarity layer).  (b) Feferman [F1] §4 itself, for the verbatim
quantifier rules.  (c) Otto's single-sorted relativized-quantifier reformulation, if the many-sorted
`EXT` encoding proves awkward.  None of these is required before the restart: Q1–Q4 are answered well
enough to fix the certificate.
