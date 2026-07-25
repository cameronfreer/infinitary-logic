# Lyndon interpolation (#14): statement-and-interface audit (v1)

Pre-implementation audit for issue #14, in the pattern of `docs/craig-audit.md`,
`docs/wellordering-audit.md`, and `docs/lopez-escobar-hard-audit.md`. **No Lean before the
D-points are signed off.** Primary source read directly (scans, EuDML/matwbn): E. G. K.
López-Escobar, *An interpolation theorem for denumerably long formulas*, Fund. Math. **57**
(1965) 253–272 — hereafter **LE65** — checked 2026-07-25.

## 1. Source statements (verified against the paper)

**LE65 §0 (p. 253), the property being proved.** "We say that the interpolation theorem is true
for `L_αβ` just in case that for all formulas φ, Φ of `L_αβ` if the implication φ → Φ is valid,
then there exists a formula π of `L_αβ` such that (1) φ → π and π → Φ are valid, (2) if a
variable occurs free in π, then it occurs free both in φ and Φ, and (3) **if a relational symbol
occurs (occurs positively, occurs negatively) in π, then it occurs (occurs positively, occurs
negatively) both in φ and in Φ.**" Craig and Lyndon are cited for `L_ωω`; the paper proves it
for `L_ω₁ω`.

**LE65 Theorem 4.1 (p. 267), the formula form — this is our target.** If `φ → Φ` is a valid
formula of `L_ω₁ω`, there is π with

* (.1) `φ → π` and `π → Φ` valid,
* (.2) `FV(π) ⊆ FV(φ) ∩ FV(Φ)`,
* (.3) if the equality symbol occurs in π, then it occurs in `φ → Φ`,
* (.4) if a relational symbol has a positive (negative) occurrence in π, then it has a positive
  (negative) occurrence **both in φ and in Φ**.

**LE65 Theorem 4.0 (p. 266), the sequent form — the orientation check.** For a valid sequent
`X → Y` and partitions `(A₁, A₂)`, `(B₁, B₂)`, the interpolating formula φ satisfies, besides
provability of `A₁ → B₁ ∪ {φ}` and `A₂ ∪ {φ} → B₂`: "(.4) if a relational symbol has a positive
(negative) occurrence in φ, then it has a positive (negative) occurrence in `A₂ → B₂` **and a
negative (positive) occurrence in `A₁ → B₁`**." The **flip between the two sides** is explicit in
the source, and it is exactly the orientation our two-coordinate engine needs (D4).

**LE65 §2 (p. 255), the language.** Symbols are ω₁ individual variables, the equality symbol,
and relational symbols; "the atomic formulas of `L_ω₁ω` are of the form `v = w` or
`P_n v₀…v_{ν_n−1}`". **No function symbols and no constants** — the source's own scope is
purely relational, matching issue #14's day-one scope.

**Equality in LE65 — a genuine ambiguity, resolved conservatively.** Footnote (3) on p. 255: "For
the purposes of this paper the equality symbol is not considered to be a relational symbol",
while Definition 2.4 (p. 257) defines positive/negative occurrence for "a relational symbol `P_n`
(equality symbol `=`)" and Definition 2.5's *positive formula* asks that "neither the equality
symbol nor any relational symbol has a negative occurrence". Conditions (.3)/(.4) then treat the
two differently: **equality gets a plain occurrence condition, polarity constrains relation
symbols only.** For first-order logic the same ambiguity was later cleaned up by Motohashi,
*Equality and Lyndon's interpolation theorem*, JSL **49** (1984) 123–128, which proves the
Lyndon theorem for logic *with* equality (Lyndon had written that the theorem "takes the same
form whether or not we admit a predicate denoting identity"). Our decision (D1/D3) is the safe
reading: **equality is logical, unconstrained in the interpolant, and absent from the polarity
sets.**

**Scope fences read off the source.**

* LE65 p. 254 and Theorem 6.3: "unlike the case of `L_ωω`, the interpolation theorem is **not**
  true for *sets* of formulas of `L_ω₁ω`" — there are disjoint `PC_Δ(L_ω₁ω)` classes not
  separable by a class closed under `L_ω₁ω`-elementary equivalence. **No theory/set-level Lyndon
  separation may be claimed** (the project's Craig separation is sentence-level, as required).
* LE65 Theorem 5.1 (p. 269), the *homomorphism theorem*: a sentence of `L_ω₁ω` is preserved under
  homomorphisms iff it is equivalent to a positive sentence ("mutatis mutandis Lyndon [10]").
  A natural corollary of #14's machinery — **explicitly not claimed by #14** (see §3).
* Ceiling: Malitz showed Craig interpolation fails in `L_κω` for `κ > ω₁`; so nothing here
  generalizes upward past `ω₁`.

**Route note.** LE65's proof is *proof-theoretic* (a cut-free Gentzen system for `L_ω₁ω`,
Theorem 3.16 completeness, then induction on derivations). The project's #8 engine is
*model-theoretic* (support-parameterised inseparability + a consistency property + the
generated-universe Henkin completion). We therefore **refine our own engine** rather than port
LE65's calculus; the source is used for the statement and for the orientation of the polarity
conditions.

## 2. Decision points

### D1 — the exact theorem, equality, and constants/functions [proposed]

Target = LE65 Theorem 4.1 specialised to sentences, over a **relational** language:
polarity-refined Craig, equality logical and unconstrained. (.2) is vacuous for sentences; (.3)
is **deliberately dropped** (see D3) — the project's occurrence machinery ignores `.equal`
entirely, so LE's equality-occurrence condition would need a new `equalityIn` recursion. That is
a self-contained later add-on, not a prerequisite.

Constants and functions are **absent from the source**. Our statements keep the ordinary Craig
sharing condition for functions (`functionsIn ⊆ ∩`) so that the endpoint reads uniformly and the
eventual relationalization wrapper (D6) has a target; no polarity claim is ever made about
function or constant symbols.

### D2 — polarity representation: **signed traversal**, not an NNF syntax [proposed]

```lean
def BoundedFormulaω.relationsInSigned {α : Type} :
    ∀ {n : ℕ}, Bool → L.BoundedFormulaω α n → Set (Σ n, L.Relations n)
  | _, _, .falsum   => ∅
  | _, _, .equal _ _ => ∅                       -- equality is logical
  | _, s, .rel R _  => if s then {⟨_, R⟩} else ∅
  | _, s, .imp φ ψ  => relationsInSigned (!s) φ ∪ relationsInSigned s ψ   -- antecedent flips
  | _, s, .all φ    => relationsInSigned s φ                              -- quantifier preserves
  | _, s, .iSup φs  => ⋃ i, relationsInSigned s (φs i)                    -- ⋁ preserves
  | _, s, .iInf φs  => ⋃ i, relationsInSigned s (φs i)                    -- ⋀ preserves

abbrev positiveRelationsIn (φ) := relationsInSigned true φ
abbrev negativeRelationsIn (φ) := relationsInSigned false φ
```

Why this and not a separate NNF inductive plus `toNNF`/`realize_toNNF`:

1. **`.not` needs no clause.** `φ.not = φ.imp falsum`, so `positive (φ.not) = negative φ` and
   `negative (φ.not) = positive φ` fall out of the `imp` clause (up to `∪ ∅`).
2. **No semantic obligation.** An NNF transform owes a realization theorem and a polarity-
   preservation theorem; the signed traversal owes neither — it is a definition on the existing
   syntax, so every existing consumer keeps working.
3. **Craig is recovered at the occurrence level**: `relationsIn φ = positiveRelationsIn φ ∪
   negativeRelationsIn φ` (one induction), so `lyndon_interpolation → craig_interpolation` is a
   set-theoretic corollary, not a re-proof.
4. **The engine never normalises anything.** In the inseparability route the interpolant is *not
   constructed*; the separator class is a hypothesis, and the fields only ever *add subformulas*
   to a side. Every such step is a sign-tracked subformula step, which is precisely what the
   traversal computes. An NNF artefact would exist only to be discarded.
5. **Mechanical twins.** The existing occurrence calculus is exactly reproducible: for each of
   `relationsIn_{not, and, top, ex, castLE, relabel, mapLanguage, abstractConst, stripConsts,
   einf, existsBlock, forallBlock, countable}` there is one signed statement, with `not`/`ex`
   becoming *swaps* rather than identities. Same for the `baseRelationsIn_*` family
   (`_falsum, _constEq, _relInst, _not, _imp_left/right/subset, _component_iInf/iSup,
   _instConst_subset, _genEx, _iSup_subset, _mapLanguage_withConstants`).

Consumer check (the user's condition "prefer the signed traversal if it supports every
consumer"): the consumers are (a) the separator class in `InsepAt`, (b) the side bounds
`SentBnd`, (c) the root gate's `stripConsts`, (d) `relationsIn`-based Craig statements, (e) the
future #15 quantifier classes. (a)–(d) are all set-membership conditions on the traversal's
output. (e) is a *different* traversal on the same pattern (sign-tracked `all`-occurrences), so
the pattern generalises; #15 does **not** need an NNF datatype either.

### D3 — the frozen endpoint [proposed]

```lean
theorem lyndon_interpolation_relational [L.IsRelational] (φ ψ : L.Sentenceω)
    (h : Sentenceω.Entails φ ψ) :
    ∃ θ : L.Sentenceω,
      θ.functionsIn ⊆ φ.functionsIn ∩ ψ.functionsIn ∧
      θ.positiveRelationsIn ⊆ φ.positiveRelationsIn ∩ ψ.positiveRelationsIn ∧
      θ.negativeRelationsIn ⊆ φ.negativeRelationsIn ∩ ψ.negativeRelationsIn ∧
      Sentenceω.Entails φ θ ∧ Sentenceω.Entails θ ψ
```

(The `functionsIn` conjunct is vacuous under `[L.IsRelational]` and is kept so the statement is
stable when the relationalization wrapper lands.) Craig for the same roots follows by
`relationsIn = pos ∪ neg` and `Set.union_subset_union`. **Not claimed**: any condition on
equality occurrences, any polarity condition on function symbols, any theory-level form.

### D4 — field-by-field kernel audit: what becomes polarity-aware [proposed]

The audit's central claim: **exactly one definition changes, and the Henkin kernel does not move
at all.**

| Kernel item | Verdict |
|---|---|
| `InsepAt F R A Γ Δ` (`Inseparability.lean`) | **Changes.** `LyndonInsepAt F P N A Γ Δ`: no separator σ with `baseFunctionsIn σ ⊆ F`, `basePositiveRelations σ ⊆ P`, `baseNegativeRelations σ ⊆ N`, support `⊆ A`, `Γ ⊨ σ`, `Δ ⊨ σ.not` |
| `SentBnd F R` (`PairedInsepFamily.lean`) | **Changes.** `SentBndPol F P N` = base functions in `F`, base positives in `P`, base negatives in `N` |
| Family invariant `PairedInsepFamilyMem` | **Changes only in its parameters**: `Γ ⊆ SentBndPol F₁ P₁ N₁`, `Δ ⊆ SentBndPol F₂ P₂ N₂`, and the separator class becomes `(F₁ ∩ F₂, P₁ ∩ N₂, N₁ ∩ P₂)` — the **flip on the Δ coordinate**, matching LE65 Thm 4.0(.4) |
| `insepAt_swap` (`PairedInseparability.lean`) | **Changes shape**: `LyndonInsepAt F P N A Γ Δ → LyndonInsepAt F N P A Δ Γ` (its separator map is `σ ↦ σ.not`, which exchanges the classes). The one-sided closures are already parametric in `(F, R)`; making them parametric in `(F, P, N)` lets every Δ-case instantiate at swapped classes — **no duplicated right-coordinate proofs** |
| `insepAt_imp_dichotomy` (C1) | **Polarity-clean, no new idea.** Its separator is `(σ₁.not).imp σ₂`; the double flip cancels: `pos = pos σ₁ ∪ pos σ₂`, `neg = neg σ₁ ∪ neg σ₂`. This is the mixed closure of the stop/go gate (D7) |
| `insepAt_iSup_component`, `insepAt_neg_iInf_component` (C3′/C4) | **Clean**: separator `iSup σ`, sign-preserving componentwise |
| `insepAt_insert_of_shared_entails` (cross gates b/c) | **The only flipped-antecedent construction**: separator `σ.imp ρ`, so the shared σ enters with reversed polarity. At **all four call sites** (shared-equality transfer and cross-coordinate `rel_congr`) σ is a `constEq` atom, whose polarity sets are `∅` under D2 — so the gate is polarity-neutral **because equality is logical**. Recorded dependency: transferring a non-equality shared sentence would require σ in the swapped class |
| `insepAt_shared_contradiction` (global C0) | **Clean**: separator is φ itself; `φ ∈ SentBndPol₁` and `φ.not ∈ SentBndPol₂` give `pos φ ⊆ P₁ ∩ N₂`, `neg φ ⊆ N₁ ∩ P₂` — exactly the refined class |
| `insepAt_grow_fresh`, `insepAt_witness_of_insepAt_genEx` (C7) | **Clean**: separator `genEx c σ` = `¬∀¬` of an abstraction — two flips cancel; needs the signed `abstractConst` twin |
| `insepAt_mono_support`, `insepAt_insert_of_entails` | **Clean**: separator unchanged |
| CP fields C0a, C1′, C2, C3, C4′ | **Clean**: each adds a *subformula* of a side sentence; the signed calculus gives the side bound (e.g. `pos (φ.imp ψ) ⊆ P` yields `pos (φ.not) = neg φ ⊆ P`) |
| CP fields `eq_refl`, `eq_symm`, `eq_trans` | **Trivial**: added sentences are `constEq` atoms with empty polarity sets |
| CP field `rel_congr` | **Clean**: added `relInst R (update g i b)` has `pos = {R}`, `neg = ∅`, and `R ∈ P_side` from the premise atom |
| CP fields `all_inst`, `neg_all_witness` | **Clean**: `instConst` is a substitution — signed sets unchanged (signed `instConst` twin) |
| `RootGate.lean` | **Needs twins**: signed `stripConsts` lemmas, then `base_interpolant_of_empty_support_separator` returns the two polarity bounds instead of one |
| `Henkin/CountableCompletion/*` (`GeneratedUniverse`, `FairEnumeration`, `QuotientTermModel`, `QuotientTruthLemma`), `ConsistencyPropertyEqOn` | **Untouched.** Polarity lives entirely inside the separator class; no CP *field shape* changes, so the completion, the term model, and the truth lemma are consumed exactly as #8 built them |

Consequence for scope: #14 is a *refinement layer* over #8 — new occurrence calculus, a
re-parameterised inseparability predicate, and a re-verified family. **The 16 CP fields are
re-verified, not re-invented**, and no part of the Henkin construction is reopened.

### D5 — semantic monotonicity as an early acceptance gate [proposed]

```lean
theorem realize_mono_of_signed [L.IsRelational] (φ : L.BoundedFormulaω α n) :
    ∀ (S₁ S₂ : L.Structure M),
      (∀ p ∈ φ.positiveRelationsIn, ∀ v, RelMap[S₁] p.2 v → RelMap[S₂] p.2 v) →
      (∀ p ∈ φ.negativeRelationsIn, ∀ v, RelMap[S₂] p.2 v → RelMap[S₁] p.2 v) →
      Realize[S₁] φ v xs → Realize[S₂] φ v xs
```

Induction on φ, **generalised over the ordered pair of structures**: the `imp` case applies the
inductive hypothesis to `(S₂, S₁)`, which is exactly why the statement must quantify over both
structures rather than fix them in the context. This is the semantic content of the polarity
definition (if it is wrong, this fails immediately) and is the first thing to prove after the
calculus. It is also the shape #15 reuses with "grow the relations" replaced by "pass to an
extension". LE65 Theorem 5.1 (homomorphism preservation) is the natural downstream consumer and
stays a **non-goal** here.

### D6 — relationalization audit [proposed, deferred unit]

For a future function-symbol wrapper the obligations are exactly:

1. `relationalizeFormula` preserves **base**-relation polarity on the nose: the translation of an
   atom `R(t⃗)` has `R` positively only, and the translation commutes with all connectives, so
   `positiveRelationsIn (relationalize φ) ∩ baseImage = baseImage '' positiveRelationsIn φ` and
   likewise negatively. This is a signed twin of the existing `relationsIn_relationalizeFormula`
   identity.
2. Graph relations `G_f` may occur with **both** polarities (the functionality axioms use them
   negatively). That is harmless **iff** they are eliminated: `backTranslateFormula` rewrites
   `G_f(x⃗, y)` to `f(x⃗) = y`, an **equality**, which D2/D3 leave unconstrained. So the
   interpolant's polarity conditions survive back-translation.
3. Function and constant symbols keep the ordinary shared-occurrence condition; no polarity claim.

Verdict: this is a late unit, gated on obligation 1; the day-one endpoint stays relational, and
the wrapper is stated only if all three check out.

### D7 — stop/go gate and unit order [proposed]

**Stop/go**: after the calculus, prove *only* the polarity forms of `insepAt_imp_dichotomy`,
`insepAt_insert_of_shared_entails`, and `insepAt_swap` — the genuinely mixed
implication/inseparability closures — **before** touching the 16-field family. If the imp
dichotomy's bookkeeping fails (i.e. `(σ₁.not).imp σ₂` does not stay in the refined class), stop:
fallbacks, in order, are (a) split the class into a pair of one-sided classes and carry both, (b)
restrict the first endpoint to *positive* interpolants only (LE65 Def 2.5's positive formulas),
(c) reconsider a proof-theoretic route via LE65's sequent calculus — a different project.

Unit order (each a compile-gated commit; later units untouched if an earlier one stalls):

0. signed traversal + the full occurrence/`base`-occurrence calculus + `relationsIn = pos ∪ neg`;
1. **D5 semantic monotonicity gate**;
2. **D7 mixed-closure gate** (three lemmas, nothing else);
3. `LyndonInsepAt` / `SentBndPol` and the one-sided closures re-parameterised at `(F, P, N)`;
4. the polarity-aware paired family + `ConsistencyPropertyEqOn` instance (Henkin kernel consumed
   unchanged) + paired model existence;
5. root-gate twins + `lyndon_interpolation_relational` + the Craig corollary;
6. facade, blueprint node, headline guard, docs.

## 3. Non-goals (recorded to prevent scope creep)

* **No NNF inductive or `toNNF` transform** anywhere in #14.
* **No theory/set-level Lyndon or PC separation** — LE65 Theorem 6.3 refutes it for `L_ω₁ω`.
* **No equality-occurrence condition** (LE65 (.3)) in the first endpoint; optional later add-on.
* **No polarity claim for function or constant symbols**, and no function-symbol wrapper before
  D6's obligation 1 is proved.
* **No homomorphism-preservation theorem** (LE65 Thm 5.1) — a separate follow-on.
* **No #15 API growth inside #14**: the universal/existential syntax classes and the
  substructure/extension preservation lemmas stay out. #14 exports only the signed-traversal
  pattern and the D5 proof shape, which #15 may imitate on quantifiers.
