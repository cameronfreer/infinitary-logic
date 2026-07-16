# Undefinability of well-ordering (#12): statement-and-interface audit (v1)

Pre-implementation audit for issue #12, in the pattern of `docs/craig-audit.md` /
`docs/fragments-audit.md`. Source: Marker, *Math 512 lecture notes* §4.4 (pp. 49–50), checked
against the actual text on 2026-07-16. Status: **awaiting review; nothing frozen.**

## 1. Source statements (verified against the PDF)

Throughout §4.4, `τ = {<, …}` — a countable vocabulary containing a distinguished binary
relation symbol `<`.

**Theorem 4.26.** Suppose `φ` is an `L_ω₁ω`-sentence and for all `α < ω₁` there is `M ⊨ φ`
where `(α, <)` embeds into `<^M`. Then there is `N ⊨ φ` where `(ℚ, <)` embeds into `<^N`.

**Corollary 4.27 (boundedness).** If `φ` is an `L_ω₁ω`-sentence and `<^M` is well-ordered for
all `M ⊨ φ`, then there is `α < ω₁` such that `<^M` has order type at most `α` for all
`M ⊨ φ`.

**Proof skeleton of 4.26 (the consistency property).** Add a countable set `C` of new
constants and distinct constants `D = {d_q : q ∈ ℚ}`. Let `Σ` be all sets of the form

    σ₀ ∪ {φ} ∪ {d_q < d_r : q < r}

where `σ₀` is a *finite* set of sentences using only finitely many constants from `C ∪ D`,
such that, writing `θ(c̄, d_{i₁}, …, d_{i_m}) = ⋀_{ψ ∈ σ₀} ψ` with `i₁ < … < i_m`, **for all
`α < ω₁`** there is `M` with property (*):

    M ⊨ φ ∧ ∃x̄ θ(x̄, b₁, …, b_m),   A ⊆ M well-ordered by <^M,   b̄ ∈ A,
    α ≤ b₁,  b₁ + α ≤ b₂,  …,  b_{m-1} + α ≤ b_m        (the α-GAP invariant)

(the inequalities are about positions in the well-order `A` — each `b` sits at least `α` above
its predecessor). Taking `σ₀ = ∅` shows `{φ} ∪ {d_q < d_r : q < r} ∈ Σ` from the hypothesis.
Marker verifies only two closure conditions and leaves the rest as **Exercise 4.28** (so the
bulk of the verification has *no source proof* — we do it ourselves):

* **C4 (disjunction)**: for `⋁_{ψ∈X} ψ ∈ σ`, each `α` has a witnessing `ψ_α ∈ X`; some `ψ`
  works for **uncountably many** `α`; and "(*) for `α` implies (*) for all `β < α`" (downward
  closure), so that `ψ` works for all `α`. — Needs the regularity/pigeonhole of `ω₁`
  (uncountably many `α` land on one of countably many `ψ`).
* **C7c (fresh witness for `t = d_r`, `i_s < r < i_{s+1}`)**: pick fresh `c ∈ C`; given `α`,
  pick `β > α + α` and apply (*) at `β`; set `b = b_s + α`; then `b_s + α ≤ b` and
  `b + α ≤ b_{s+1}` — the new point is inserted **inside a gap**, restoring the invariant at
  `α`. This is the density engine.

Model existence for `Σ` yields `N ⊨ φ` realizing the full positive diagram
`{d_q < d_r : q < r}`.

**Corollary 4.34 is a different machine.** The uncountable version (a model of size `ℵ₁` with
a `(ℚ,<)`-embedding, from one model with `<` of order type `ω₁`) is proved from **Keisler's
elementary-end-extension theorem** (Theorem 4.30, via omitting types) iterated `ω₁` times
(Corollary 4.31) — the §4.5 machinery, none of which the repository has. Recommendation:
**scope 4.34 out of #12** (see D7).

## 2. Statement precision (issue #12 + source, sharpened)

The issue's precision note says the theorem produces an "injective order-preserving map"
because only the **positive** diagram is inserted. The source-honest raw conclusion is in fact
slightly weaker: the term model gives `f : ℚ → N` with `q < r → f q <^N f r` — a strict-order
**homomorphism**. Injectivity is *not* automatic for arbitrary `φ` (if `f q = f r` with
`q < r`, picking `s ∈ (q,r)` yields only a `<^N`-2-cycle, contradictory only when `<^N` is a
strict order). Proposal:

* state the core theorem with the raw conclusion `∀ q r, q < r → f q <^N f r`;
* add the injectivity corollary under the hypothesis that `<^N` is (or `φ` entails) a strict
  partial order — and note injectivity is automatic in the boundedness corollary 4.27, where
  `<^M` is well-ordered. A full induced-substructure/relational-embedding strengthening stays
  out (per the issue: it is not what the displayed proof gives).

## 3. Target Lean statements (draft — for review, names provisional)

```
-- hypothesis form (D1): for every countable ordinal, a model with an α-chain
def HasWellOrderedChains (φ : L.Sentenceω) (lt : L.Relations 2) : Prop :=
  ∀ α : Ordinal, α < ω₁ → ∃ (M : Type) (_ : L.Structure M) (_ : Nonempty M),
    Sentenceω.Realize φ M ∧ ∃ e : α.toType → M, StrictMonoOn-with-respect-to (RelMap lt) e

theorem exists_rational_chain_of_wellOrderedChains
    (φ : L.Sentenceω) (lt : L.Relations 2) (h : HasWellOrderedChains φ lt) :
    ∃ (N : Type) (_ : L.Structure N) (_ : Nonempty N), Sentenceω.Realize φ N ∧
      ∃ f : ℚ → N, ∀ q r : ℚ, q < r → RelMap lt ![f q, f r]      -- raw positive form (§2)

theorem wellOrder_boundedness  -- Corollary 4.27
    (φ : L.Sentenceω) (lt : L.Relations 2)
    (hwo : ∀ M [L.Structure M] [Nonempty M], Sentenceω.Realize φ M → IsWellOrder-on (RelMap lt)) :
    ∃ α < ω₁, ∀ M …, Sentenceω.Realize φ M → orderType (RelMap lt on M) ≤ α
```

Undefinability of well-ordering is then the one-line reading of 4.27 (no single `φ` can have
exactly the well-ordered `<`-models of unbounded countable type — e.g. no `φ` axiomatizes
"`<` is a well-order" over `(α, <)`-expansions).

## 4. Asset inventory (what the repository already has)

* **The kernel (#8 milestone 1, as the issue predicted)**: `ConsistencyPropertyEqOn U` +
  `HenkinComplete` (Interpolation/ConsistencyPropertyEqOn.lean), the fair enumeration
  `exists_henkinComplete` (FairEnumeration.lean), and the forward-polarity term model
  `exists_model_of_henkinComplete` (QuotientTermModel/QuotientTruthLemma.lean) — **relational
  base `L[[ℕ]]`, `[L.IsRelational]`**.
* **The arbitrary-language lift, for free (post-#8 bonus)**: the Layer 3 relationalization
  (`relationalizeFormula`, `graphAxioms`, `reconstructStructure`, `realize_*` bridges).
  `<` is a *relation*, and both `graphExpansion` and `reconstructStructure` preserve base
  relations on the nose — so both the hypothesis and the `ℚ`-chain conclusion transport.
  Recommended route (D5): prove the core over a relational `L`, lift to arbitrary `L` by
  relationalizing `φ` (the well-ordered-chain hypothesis for `Ax(F) ∧ φʳᵉˡ` follows from the
  hypothesis for `φ` via graph expansion; the conclusion returns via reconstruction).
* **Ordinal machinery**: `Ordinal.{0}`, `ω₁` handling, `toType`, cofinality/regularity
  (`Cardinal.isRegular_aleph_one` for the C4 pigeonhole) — all exercised by the
  HanfSpectrum/Scott work. Ordinal gap arithmetic (`b + α`) is Mathlib-native.
* **ℚ**: Mathlib's `ℚ` is a countable dense `LinearOrder`, `Encodable` — nothing needed.
* **Constants**: the kernel's constants are `ℕ`-indexed (`L[[ℕ]]`, `constTerm : ℕ → _`).

## 5. Gaps and risks (ranked)

1. **Member shape (the one real interface question).** Marker's `Σ`-members are *countable*
   sets — every member contains the full infinite positive diagram `{d_q < d_r : q < r}` plus
   `{φ}`. The Craig instantiation of the kernel used finite-condition families over a
   generated universe with finite roots. Audit question to resolve before coding: does
   `ConsistencyPropertyEqOn`/`exists_henkinComplete` already tolerate (a) countable members
   and (b) a countable *root* set (we need `S* ⊇ {φ} ∪ diagram`), or do we relativize — treat
   `{φ} ∪ {d_q < d_r}` as a fixed base theory carried inside the (*)-condition, with members =
   finite `σ₀` only, and fold the base into the roots by fair-enumeration requests? The second
   mirrors the Craig pattern and is the expected answer; the first would be a small kernel
   generalization. **This is the analogue of Craig's D3 and must be frozen first.**
2. **Exercise 4.28.** Only C4 and C7c have source proofs; every other closure condition
   (C0–C3, the equality conditions, the remaining quantifier cases) is ours. The (*)-invariant
   must be shown stable under each decomposition — expect the same kind of per-field grind as
   `InsepFamilyMem`, with the α-gap bookkeeping in place of finite support.
3. **The (*) representation (D6).** "b̄ ∈ A well-ordered with α-gaps" needs a Lean shape:
   proposal — an order-embedding `g : (α·m + …).toType ↪` … no; cleaner: carry the tuple
   positions abstractly as `∃ (β̄ : Fin m → Ordinal)` with `α ≤ β₁`, `βᵢ + α ≤ βᵢ₊₁` and an
   order-embedding of `(β_m + 1).toType` into `<^M` sending `βᵢ` to `bᵢ`. Freeze at review.
4. **Two constant families on an `ℕ`-indexed kernel.** `C ∪ D ↪ ℕ` by parity coding
   (`D = {d_q}` on evens via an enumeration `ℚ ≃ ℕ`, fresh `C` on odds). Bookkeeping only,
   but it leaks into freshness arguments (C7c needs "c not yet used") — the Craig
   finite-support calculus (`sentenceJConsts`) is exactly the right tool and is already
   neutral.
5. **Downward closure of (*)** ("if ψ works for α it works for all β < α") — needs the gap
   inequalities to be monotone in α; true but must be stated carefully with ordinal `+`
   (left-monotonicity `β ≤ α → b + β ≤ b + α` holds; fine).
6. **Relational-first lift (D5)** — believed routine given Layer 3, but the hypothesis
   transport direction "models of `Ax ∧ φʳᵉˡ` with α-chains" must quantify over *graph*
   models, where reconstruction (not expansion) produces the `L`-model; check no `Nonempty`/
   countability friction.

## 6. Decision points (to freeze at review)

| # | Decision | Proposal |
|---|---|---|
| D1 | hypothesis form | `∀ α : Ordinal, α < ω₁ → ∃ M …, Realize φ M ∧ ∃ e : α.toType → M` strictly `lt`-monotone; `Type 0` carriers, `[Nonempty M]`, matching the entailment convention |
| D2 | conclusion form | raw positive `q < r → RelMap lt ![f q, f r]`; injectivity corollary under strict-order hypothesis; well-order corollary gets it free |
| D3 | constants | parity coding `C ⊕ D ↪ ℕ` over the existing `L[[ℕ]]` kernel; `D`-indexing via a fixed `ℚ ≃ ℕ` |
| D4 | member shape | finite `σ₀`-conditions relative to the base `{φ} ∪ positive diagram` (Craig-style), base delivered through roots/requests — pending the §5.1 kernel check |
| D5 | language scope | relational core first on the kernel; arbitrary-`L` endpoint via the Layer 3 relationalization |
| D6 | (*) gap representation | ordinal-position form of §5.3 |
| D7 | scope split | 4.26 + 4.27 (+ undefinability reading) = #12; **Corollary 4.34 deferred** to a future elementary-end-extensions arc (Keisler 4.30/4.31, omitting-types iteration — new issue) |

## 7. Proposed unit sequence (gated, Craig-style)

1. **U1 — statement layer**: `HasWellOrderedChains`, the (*) predicate with the gap invariant,
   downward closure, and the `σ₀ = ∅` instance from the hypothesis. Pure statements + easy
   lemmas; freezes D1/D6 in code.
2. **U2 — kernel-interface resolution** (D4): either the base-theory-relativized family or the
   countable-members generalization; acceptance = `Σ` typechecks as a
   `ConsistencyPropertyEqOn`-style family with the two source-verified fields (C4 via `ω₁`
   pigeonhole, C7c via gap insertion) proved.
3. **U3 — Exercise 4.28**: the remaining closure fields.
4. **U4 — model extraction**: fair enumeration + term model → relational
   `exists_rational_chain_of_wellOrderedChains`.
5. **U5 — corollaries**: boundedness 4.27 (well-order hypothesis → injectivity free →
   contradiction with unbounded types), undefinability packaging, injectivity corollary.
6. **U6 — arbitrary-language lift** (D5) + facade/blueprint/guard/docs sweep.
