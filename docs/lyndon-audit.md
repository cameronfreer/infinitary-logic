# Lyndon interpolation (#14): statement-and-interface audit (v2, FROZEN)

Pre-implementation audit for issue #14, in the pattern of `docs/craig-audit.md`,
`docs/wellordering-audit.md`, and `docs/lopez-escobar-hard-audit.md`. Primary source read
directly (scans, EuDML/matwbn): E. G. K. López-Escobar, *An interpolation theorem for denumerably
long formulas*, Fund. Math. **57** (1965) 253–272 — hereafter **LE65** — checked 2026-07-25.

## STATUS: COMPLETE (2026-07-26)

All eight units landed, each compile-gated and axiom-clean; endpoint `lyndon_interpolation`
(arbitrary language, no hypotheses) on the default surface.

| Unit | Files | Outcome |
|---|---|---|
| 0 | `Lomega1omega/Polarity`, `Methods/PolarityCalculus` | signed traversal + full occurrence/base calculus; **no NNF anywhere** |
| 1 | `Lomega1omega/PolaritySemantics` | `realize_mono_of_signed` — the semantic gate **passed**; the `imp` case closes through the swapped structure pair |
| 2 | `Interpolation/LyndonInseparability` | `LyndonInsepAt` + the three mixed gates; the C1 separator `(σ₁.not).imp σ₂` is polarity-clean by double-flip cancellation; `lyndon_root_class_eq` |
| 3 | `Interpolation/LyndonClosures` | `SentBndPol` with the **directional** rules (negation *exchanges* the classes) + the one-sided closures; `relInst` positive-only as an iff |
| 4 | `Interpolation/LyndonPairedFamily`, `LyndonPairedCP` | the flipped-class paired invariant, mixed `C0`, the sixteen CP fields, `exists_lyndon_paired_model_neg` |
| 5 | `Interpolation/LyndonRootGate`, `LyndonRelational`, `LyndonSublanguage` | signed root gate; countable core (root-class equation **cited**, load-bearing); `lyndon_interpolation_relational` |
| 6 | `Interpolation/LyndonRelationalize` | the D6 gate: base-polarity preserved on the nose; graph atoms back-translate into **equalities**, so arbitrary graph polarity vanishes |
| 7 | `Interpolation/LyndonArbitrary` | `lyndon_interpolation` + `craig_of_lyndon_interpolation` |
| 8 | facade / blueprint / docs / release | `ModelTheory/LyndonInterpolation`, nodes `thm:lyndon{,-relational}`, headline + cone guards, v1.7.0 |

Predictions vs outcome. **D2 held**: the signed traversal supported every consumer and no
negation-normal form was ever needed — the engine only ever adds *subformulas*, which is exactly
what a sign-tracked traversal computes. **D4c held and mattered**: the flipped-antecedent gate is
the only one needing swapped-class hypotheses, and its four call sites all transfer *equality*
atoms, whose polarity sets are empty — so equality-as-logical is load-bearing, not cosmetic.
**D6 held**: base-relation polarity is preserved exactly, and the graph relations' arbitrary
polarity is harmless because back-translation turns them into equalities. Two things the audit did
not foresee: the `neg_all_witness` field needs three further signed C7 consumers (`insert_congr`,
`instConst_of_ex`, `not_instConst_of_not_all`), and the whole relationalization gate had to be
proved in **membership** form, because `relationsInSigned` and `baseRelSym` land in definitionally
equal but syntactically distinct `Sigma` types that block `rw` on the set-algebra lemmas.

Status: **v2, FROZEN per review 2026-07-25.** Changes from v1: the endpoint is named the
*relation-polarity / logical-equality form* of LE65 Theorem 4.1 rather than the theorem as printed
(§D1); the root orientation is now an **acceptance equation** (§D4a); the flipped-antecedent gate
carries the swapped-class hypotheses in its *general* signature with the equality case exposed as a
corollary (§D4c); the unit order is repaired so that no gate precedes the definition it needs
(§D7); and the relationalization wrapper is **retained in #14's acceptance scope** as Units 6–7
(§D6). Implementation begins with Unit 0.

## 1. Source statements (verified against the paper)

**LE65 §0 (p. 253), the property being proved.** "We say that the interpolation theorem is true
for `L_αβ` just in case that for all formulas φ, Φ of `L_αβ` if the implication φ → Φ is valid,
then there exists a formula π of `L_αβ` such that (1) φ → π and π → Φ are valid, (2) if a
variable occurs free in π, then it occurs free both in φ and Φ, and (3) **if a relational symbol
occurs (occurs positively, occurs negatively) in π, then it occurs (occurs positively, occurs
negatively) both in φ and in Φ.**" Craig and Lyndon are cited for `L_ωω`; the paper proves it for
`L_ω₁ω`.

**LE65 Theorem 4.1 (p. 267), the formula form.** If `φ → Φ` is a valid formula of `L_ω₁ω`, there
is π with

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
the source, and it is exactly the orientation our two-coordinate engine needs (§D4a).

**LE65 §2 (p. 255), the language.** Symbols are ω₁ individual variables, the equality symbol, and
relational symbols; "the atomic formulas of `L_ω₁ω` are of the form `v = w` or
`P_n v₀…v_{ν_n−1}`". **No function symbols and no constants** — the source's own scope is purely
relational, matching issue #14's day-one scope.

**Equality in LE65 — a genuine ambiguity, resolved conservatively.** Footnote (3) on p. 255: "For
the purposes of this paper the equality symbol is not considered to be a relational symbol", while
Definition 2.4 (p. 257) defines positive/negative occurrence for "a relational symbol `P_n`
(equality symbol `=`)" and Definition 2.5's *positive formula* asks that "neither the equality
symbol nor any relational symbol has a negative occurrence". Conditions (.3)/(.4) then treat the
two differently: **equality gets a plain occurrence condition, polarity constrains relation
symbols only.** For first-order logic the same ambiguity was later cleaned up by Motohashi,
*Equality and Lyndon's interpolation theorem*, JSL **49** (1984) 123–128, which proves the Lyndon
theorem for logic *with* equality (Lyndon had written that the theorem "takes the same form
whether or not we admit a predicate denoting identity").

**Scope fences read off the source.**

* LE65 p. 254 and Theorem 6.3: "unlike the case of `L_ωω`, the interpolation theorem is **not**
  true for *sets* of formulas of `L_ω₁ω`" — there are disjoint `PC_Δ(L_ω₁ω)` classes not separable
  by a class closed under `L_ω₁ω`-elementary equivalence. **No theory/set-level Lyndon separation
  may be claimed** (the project's Craig separation is sentence-level, as required).
* LE65 Theorem 5.1 (p. 269), the *homomorphism theorem*: a sentence of `L_ω₁ω` is preserved under
  homomorphisms iff it is equivalent to a positive sentence ("mutatis mutandis Lyndon [10]"). A
  natural corollary of #14's machinery — **explicitly not claimed by #14** (see §3).
* Ceiling: Malitz showed Craig interpolation fails in `L_κω` for `κ > ω₁`; nothing here
  generalizes upward past `ω₁`.

**Route note.** LE65's proof is *proof-theoretic* (a cut-free Gentzen system for `L_ω₁ω`,
Theorem 3.16 completeness, then induction on derivations). The project's #8 engine is
*model-theoretic* (support-parameterised inseparability + a consistency property + the
generated-universe Henkin completion). We therefore **refine our own engine** rather than port
LE65's calculus; the source is used for the statement and for the orientation of the polarity
conditions.

## 2. Decision points

### D1 — what exactly is claimed: the relation-polarity / logical-equality form [FROZEN]

The endpoint is **the relation-polarity / logical-equality form of LE65 Theorem 4.1**, *not* that
theorem as printed. Precisely:

* clause (.4) — the substantive Lyndon clause — is **retained in full**;
* clause (.1) is retained (both entailments);
* clause (.2) is vacuous, the endpoint being about sentences;
* clause (.3) — the *equality-occurrence* condition — is **deliberately dropped**: equality is
  treated as a logical symbol, unconstrained in the interpolant and absent from the polarity sets.

This is a **deliberate weakening of LE65's equality bookkeeping**, and every statement, docstring,
blueprint node, and release note must say so in those terms; nothing may describe the result as
"LE65 Theorem 4.1" without the qualifier. Restoring (.3) needs a separate `equalityIn` occurrence
recursion plus its own calculus, and is a self-contained later add-on (§3), not a prerequisite.

Constants and functions are **absent from the source**. Our statements keep the ordinary Craig
sharing condition for functions (`functionsIn ⊆ ∩`); no polarity claim is ever made about function
or constant symbols. The arbitrary-language wrapper is in scope via relationalization (§D6).

### D2 — polarity representation: **signed traversal**, not an NNF syntax [FROZEN]

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
   constructed*; the separator class is a hypothesis, and the fields only ever *add subformulas* to
   a side. Every such step is a sign-tracked subformula step, which is precisely what the traversal
   computes. An NNF artefact would exist only to be discarded.
5. **Mechanical twins.** The existing occurrence calculus is exactly reproducible: for each of
   `relationsIn_{not, and, top, ex, castLE, relabel, mapLanguage, abstractConst, stripConsts,
   einf, existsBlock, forallBlock, countable}` there is one signed statement, with `not`/`ex`
   becoming *swaps* rather than identities. Same for the `baseRelationsIn_*` family
   (`_falsum, _constEq, _relInst, _not, _imp_left/right/subset, _component_iInf/iSup,
   _instConst_subset, _genEx, _iSup_subset, _mapLanguage_withConstants`).

Consumer check: the consumers are (a) the separator class in `LyndonInsepAt`, (b) the side bounds
`SentBndPol`, (c) the root gate's `stripConsts`, (d) `relationsIn`-based Craig statements, (e) the
future #15 quantifier classes. (a)–(d) are all set-membership conditions on the traversal's
output. (e) is a *different* traversal on the same pattern (sign-tracked `all`-occurrences), so the
pattern generalises; #15 does **not** need an NNF datatype either.

### D3 — the frozen endpoint [FROZEN]

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
stable when the Unit-7 wrapper lands.) Craig for the same roots follows by
`relationsIn = pos ∪ neg` and `Set.union_subset_union`. **Not claimed**: any condition on equality
occurrences (§D1), any polarity condition on function symbols, any theory-level form.

### D4 — kernel audit: what becomes polarity-aware [FROZEN]

The audit's central claim, stated exactly: **only the separator/side-bound layer changes; the
Henkin interface and implementation remain unchanged.**

| Kernel item | Verdict |
|---|---|
| `InsepAt F R A Γ Δ` (`Inseparability.lean`) | **Changes.** `LyndonInsepAt F P N A Γ Δ`: no separator σ with `baseFunctionsIn σ ⊆ F`, `basePositiveRelations σ ⊆ P`, `baseNegativeRelations σ ⊆ N`, support `⊆ A`, `Γ ⊨ σ`, `Δ ⊨ σ.not` |
| `SentBnd F R` (`PairedInsepFamily.lean`) | **Changes.** `SentBndPol F P N` = base functions in `F`, base positives in `P`, base negatives in `N` |
| Family invariant `PairedInsepFamilyMem` | **Changes only in its parameters**: `Γ ⊆ SentBndPol F₁ P₁ N₁`, `Δ ⊆ SentBndPol F₂ P₂ N₂`, separator class `(F₁ ∩ F₂, P₁ ∩ N₂, N₁ ∩ P₂)` — the **flip on the Δ coordinate** (§D4a) |
| `insepAt_swap` (`PairedInseparability.lean`) | **Changes shape**: `LyndonInsepAt F P N A Γ Δ → LyndonInsepAt F N P A Δ Γ` (its separator map is `σ ↦ σ.not`, which exchanges the classes). The one-sided closures are already parametric in `(F, R)`; making them parametric in `(F, P, N)` lets every Δ-case instantiate at swapped classes — **no duplicated right-coordinate proofs** |
| `insepAt_imp_dichotomy` (C1) | **Polarity-clean, no new idea.** Separator `(σ₁.not).imp σ₂`; the double flip cancels: `pos = pos σ₁ ∪ pos σ₂`, `neg = neg σ₁ ∪ neg σ₂`. One of the three Unit-2 gates |
| `insepAt_iSup_component`, `insepAt_neg_iInf_component` (C3′/C4) | **Clean**: separator `iSup σ`, sign-preserving componentwise |
| `insepAt_insert_of_shared_entails` (cross gates b/c) | **Changes signature** — see §D4c. Separator `σ.imp ρ`, so the shared σ enters with reversed polarity; the *general* form must demand σ in the swapped class, and the `constEq` case is exposed as a corollary |
| `insepAt_shared_contradiction` (global C0) | **Clean**: separator is φ itself; `φ ∈ SentBndPol₁` and `φ.not ∈ SentBndPol₂` give `pos φ ⊆ P₁ ∩ N₂`, `neg φ ⊆ N₁ ∩ P₂` — exactly the refined class |
| `insepAt_grow_fresh`, `insepAt_witness_of_insepAt_genEx` (C7) | **Clean**: separator `genEx c σ` = `¬∀¬` of an abstraction — two flips cancel; needs the signed `abstractConst` twin |
| `insepAt_mono_support`, `insepAt_insert_of_entails` | **Clean**: separator unchanged |
| CP fields C0a, C1′, C2, C3, C4′ | **Clean**: each adds a *subformula* of a side sentence; the signed calculus gives the side bound (e.g. `pos (φ.imp ψ) ⊆ P` yields `pos (φ.not) = neg φ ⊆ P`) |
| CP fields `eq_refl`, `eq_symm`, `eq_trans` | **Trivial**: added sentences are `constEq` atoms with empty polarity sets |
| CP field `rel_congr` | **Clean**: added `relInst R (update g i b)` has `pos = {R}`, `neg = ∅`, and `R ∈ P_side` from the premise atom |
| CP fields `all_inst`, `neg_all_witness` | **Clean**: `instConst` is a substitution — signed sets unchanged (signed `instConst` twin) |
| `RootGate.lean` | **Needs twins**: signed `stripConsts` lemmas, then `base_interpolant_of_empty_support_separator` returns the two polarity bounds instead of one |
| `Henkin/CountableCompletion/*` (`GeneratedUniverse`, `FairEnumeration`, `QuotientTermModel`, `QuotientTruthLemma`), `ConsistencyPropertyEqOn` | **Interface and implementation unchanged.** Polarity lives entirely inside the separator class; no CP *field shape* changes, so the completion, the term model, and the truth lemma are consumed exactly as #8 built them |

Consequence for scope: #14 is a *refinement layer* over #8 — new occurrence calculus, a
re-parameterised inseparability predicate, and a re-verified family. **The 16 CP fields are
re-verified, not re-invented.**

#### D4a — the root orientation, as an acceptance equation [FROZEN]

The final instantiation is recorded here and must be discharged as a **stated equation**, not left
implicit in the assembly:

```
Γ-root:  φ       with  (P₁, N₁) = (Pos φ, Neg φ)
Δ-root:  ψ.not   with  (P₂, N₂) = (Neg ψ, Pos ψ)      -- because Pos (ψ.not) = Neg ψ, Neg (ψ.not) = Pos ψ

separator class = (P₁ ∩ N₂, N₁ ∩ P₂) = (Pos φ ∩ Pos ψ, Neg φ ∩ Neg ψ)
```

so the class the engine maintains is *literally* the pair of intersections appearing in the D3
endpoint. Acceptance: a lemma of the form

```lean
theorem lyndon_root_class_eq (φ ψ : L.Sentenceω) :
    (φ.positiveRelationsIn ∩ (ψ.not).negativeRelationsIn,
     φ.negativeRelationsIn ∩ (ψ.not).positiveRelationsIn)
      = (φ.positiveRelationsIn ∩ ψ.positiveRelationsIn,
         φ.negativeRelationsIn ∩ ψ.negativeRelationsIn)
```

is proved in Unit 2 (immediately after the signed `not`-swap lemmas) and cited at the Unit-5
assembly. This is also the machine-checkable form of LE65 Theorem 4.0(.4)'s side flip.

#### D4c — the flipped-antecedent gate: swapped-class signature + equality corollary [FROZEN]

Because

```
Pos (σ.imp ρ) = Neg σ ∪ Pos ρ        Neg (σ.imp ρ) = Pos σ ∪ Neg ρ
```

the signed gate **cannot** keep the old generic "shared σ" interface. Its general form carries the
swapped-class hypotheses:

```lean
theorem lyndonInsepAt_insert_of_shared_entails
    (hσF : σ.baseFunctionsIn ⊆ F)
    (hσP : σ.basePositiveRelations ⊆ N)     -- swapped
    (hσN : σ.baseNegativeRelations ⊆ P)     -- swapped
    (hσA : support σ ⊆ A) (hΔσ : Δ ⊨ σ) (hcons : insert σ Γ ⊨ φ)
    (h : LyndonInsepAt F P N A Γ Δ) : LyndonInsepAt F P N A (insert φ Γ) Δ
```

and the four current call sites are served by an **exposed corollary**, not by a hidden assumption
inside a generic theorem:

```lean
theorem lyndonInsepAt_insert_of_shared_constEq_entails (a b : ℕ) …
    -- discharges hσP/hσN from basePositiveRelations (constEq a b) = ∅ = baseNegativeRelations …
```

Equality's empty polarity sets make the corollary immediate; the *dependency is visible in the
signature*, so a future refactor that transfers a non-equality shared sentence is forced to supply
the swapped-class bounds rather than silently breaking the theorem.

### D5 — semantic monotonicity as an early acceptance gate [FROZEN]

```lean
theorem realize_mono_of_signed [L.IsRelational] (φ : L.BoundedFormulaω α n) :
    ∀ (S₁ S₂ : L.Structure M),
      (∀ p ∈ φ.positiveRelationsIn, ∀ v, RelMap[S₁] p.2 v → RelMap[S₂] p.2 v) →
      (∀ p ∈ φ.negativeRelationsIn, ∀ v, RelMap[S₂] p.2 v → RelMap[S₁] p.2 v) →
      Realize[S₁] φ v xs → Realize[S₂] φ v xs
```

Induction on φ, **generalised over the ordered pair of structures**: the `imp` case applies the
inductive hypothesis to `(S₂, S₁)`, which is why the statement must quantify over both structures
rather than fix them in the context. This is the semantic content of the polarity definition (if it
is wrong, this fails immediately), and it is the shape #15 reuses with "grow the relations"
replaced by "pass to an extension". LE65 Theorem 5.1 (homomorphism preservation) is the natural
downstream consumer and stays a **non-goal** here.

### D6 — relationalization: **retained in #14's acceptance scope** [FROZEN]

Issue #14's milestone 6 promised a relationalization wrapper; it stays. The obligations are:

1. `relationalizeFormula` preserves **base**-relation polarity on the nose: the translation of an
   atom `R(t⃗)` has `R` positively only, and the translation commutes with all connectives, so
   `positiveRelationsIn (relationalize φ) ∩ baseImage = baseImage '' positiveRelationsIn φ` and
   likewise negatively — a signed twin of the existing `relationsIn_relationalizeFormula` identity.
   **This is the Unit-6 stop/go gate.**
2. Graph relations `G_f` may occur with **both** polarities (the functionality axioms use them
   negatively). Harmless **iff** they are eliminated: `backTranslateFormula` rewrites `G_f(x⃗, y)`
   to `f(x⃗) = y`, an **equality**, which D1/D3 leave unconstrained. So the interpolant's polarity
   conditions survive back-translation.
3. Function and constant symbols keep the ordinary shared-occurrence condition; no polarity claim.

If obligation 1 fails, #14 does **not** silently shed the wrapper: the issue is revised
explicitly, recording that #14 closes at the source-faithful relational theorem and opening a
successor issue for the wrapper.

### D7 — stop/go gates and unit order [FROZEN, repaired]

**Unit-2 stop/go**: after the calculus, the monotonicity gate, and the *minimal* `LyndonInsepAt`
definition, prove only the polarity forms of `insepAt_imp_dichotomy`,
`insepAt_insert_of_shared_entails` (in the §D4c signature), and `insepAt_swap`, plus the §D4a root
class equation — **then stop and reassess** before any sixteen-field assembly. If the imp
dichotomy's bookkeeping fails, the fallback is (a) carry a pair of one-sided classes rather than a
single class; a proof-theoretic route via LE65's sequent calculus is a different project and not a
fallback.

*Re-scoping option, not a fallback:* restricting the endpoint to **positive interpolants only**
(LE65 Definition 2.5) would be a **weaker theorem than the stated target** — it does not complete
LE65 Theorem 4.1(.4) — and may be adopted only by an explicit issue revision, never as a silent
substitute.

Unit order (each a compile-gated commit; later units untouched if an earlier one stalls):

0. signed traversal + the full occurrence and **base**-occurrence signed calculus +
   `relationsIn = pos ∪ neg`;
1. **D5 semantic monotonicity gate**;
2. **minimal `LyndonInsepAt`**, then the three mixed gates (§D4c signature) and the §D4a root
   class equation — the stop/go point;
3. `SentBndPol` and the remaining one-sided closures re-parameterised at `(F, P, N)`;
4. the polarity-aware paired family + `ConsistencyPropertyEqOn` instance (Henkin interface and
   implementation consumed unchanged) + paired model existence;
5. root-gate twins + `lyndon_interpolation_relational` (D3) + the Craig corollary;
6. signed relationalization identities, with **base-polarity preservation as the stop/go gate**
   (§D6 obligation 1);
7. arbitrary-language `lyndon_interpolation` via the wrapper;
8. facade, blueprint node, headline guard, docs.

## 3. Non-goals (recorded to prevent scope creep)

* **No NNF inductive or `toNNF` transform** anywhere in #14.
* **No theory/set-level Lyndon or PC separation** — LE65 Theorem 6.3 refutes it for `L_ω₁ω`.
* **No equality-occurrence condition** (LE65 (.3)) in either endpoint; the endpoints are named the
  relation-polarity / logical-equality form (§D1). Restoring (.3) is a separate `equalityIn`
  development.
* **No polarity claim for function or constant symbols** — Unit 7's wrapper gives them the ordinary
  Craig sharing condition only.
* **No homomorphism-preservation theorem** (LE65 Thm 5.1) — a separate follow-on.
* **No #15 API growth inside #14**: the universal/existential syntax classes and the
  substructure/extension preservation lemmas stay out. #14 exports only the signed-traversal
  pattern and the D5 proof shape, which #15 may imitate on quantifiers.
