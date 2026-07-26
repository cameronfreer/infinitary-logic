# Malitz universal interpolation and relative preservation (#15): statement-and-interface audit (v1)

Pre-implementation audit for issue #15, in the pattern of `docs/craig-audit.md`,
`docs/wellordering-audit.md`, `docs/lopez-escobar-hard-audit.md`, and `docs/lyndon-audit.md`.
**No Lean before the D-points are signed off.**

Primary source read directly: *Infinitary Logic Has No Expressive Efficiency Over Finitary Logic*
(the "expressive-efficiency notes", arXiv 2209.05615), §2 for the `∀n`/`∃n` hierarchy and §4.2.2 for
Theorems 4.5–4.7, checked 2026-07-26.  These state and attribute Malitz's results
([Mal69] = *Universal classes in infinitary languages*, Duke Math. J. 36 (1969) 621–630) and note
that the relative form appears in Keisler [Kei71].  **Malitz 1969 and Keisler 1971 themselves are
not verified here** — see D1 for exactly what that costs.

## 1. Source statements (verified against the notes)

**The quantifier hierarchy (§2).**  For each `n`, classes `∀n`, `∃n` of `L∞ω`-formulas:

1. atomic `ψ` is in every `∀n` and every `∃n`;
2. `¬φ ∈ ∃n` iff `φ ∈ ∀n`, and dually;
3. `⋁Φ` and `⋀Φ` are in `∃n` (resp. `∀n`) if every member is — **infinite conjunctions and
   disjunctions are not counted as quantifiers at all**;
4. `∃y φ ∈ ∃n` if `φ ∈ ∃n` and `n ≥ 1`; `∈ ∃(n+1)` if `φ ∈ ∀n`;
5. `∀y φ ∈ ∀n` if `φ ∈ ∀n` and `n ≥ 1`; `∈ ∀(n+1)` if `φ ∈ ∃n`.

`∃0 = ∀0` = quantifier-free; **`∃1` = existential, `∀1` = universal**.  The notes stress that this
differs from the `Σn`/`Πn` counting (which counts infinite disjunctions as existentials): "a formula
of the form `⋀ᵢ ∃x θᵢ(x)` is `∃1` but not `Σ1`".  They also record the reason to use `∀n`/`∃n` here:
**Malitz showed a formula of `L_ω₁ω` is preserved by substructures iff it is universal (`∀1`)**.

**Theorem 4.5 (Malitz interpolation theorem [Mal69]).** "Suppose the signature `τ` has **no function
symbols**.  Let `φ, ψ` be sentence[s] of `L_ω₁ω` such that `ψ` is universal (`∀1`), and `φ ⊨ ψ`.
Then, there is a **universal** sentence `θ` of `L_ω₁ω` such that `φ ⊨ θ`, `θ ⊨ ψ` and **every symbol
occurring in `θ` occurs in both `φ` and `ψ`**."

Note the symbol condition is the plain **Craig** one — shared occurrence, *not* polarity-refined.
#15 is therefore orthogonal to #14: it refines the *quantifier* shape, not the *sign*.

**Theorem 4.6 (Malitz [Mal69]; relative version in Keisler [Kei71]), which "applies to any
signature `τ`".**  For sentences `φ, σ` of `L_ω₁ω`, TFAE:

1. if `A ⊂ B`, `A ⊨ σ`, `B ⊨ σ`, and `A ⊨ φ`, then `B ⊨ φ`;
2. there is an **existential** sentence `θ` of `L_ω₁ω` with `σ ⊨ φ ↔ θ`.

**Fences read off the source.**

* **Function-free scope of 4.5**: the interpolation theorem is stated only for signatures with no
  function symbols, while 4.6 is stated for any signature.  That asymmetry is real and D5 explains
  why our machinery reproduces it.
* **Only `L_ω₁ω` (and `L_ωω`)**: Malitz [Mal71] showed Craig interpolation fails in `L_κω` for
  `κ > ω₁`, "and indeed there are examples with no interpolant in `L∞ω`".
* **The set/theory-level form is FALSE for `L_ω₁ω`**: "there is a set of `L_ω₁ω` sentences closed
  under substructures which is not equivalent to any set of universal `L_ω₁ω` sentences" (it is
  equivalent to a universal `L_ω₂ω` sentence).  This is the #15 analogue of the LE65 Theorem 6.3
  fence in #14: **no theory/set-level preservation theorem may ever be claimed.**
* **The two-sided version does not relativize**: Malitz shows a formula preserved both upwards and
  downwards is equivalent to a quantifier-free sentence, "but this is **not** true relative to a
  sentence `σ`".  So no mod-`σ` quantifier-free two-sided claim.

## 2. Decision points

### D1 — freeze the statements before any Lean predicate [proposed]

Two endpoints, in this order (D7):

```lean
theorem malitz_relative_preservation (σ φ : L.Sentenceω) :
    (∀ (A B : Type) [L.Structure A] [L.Structure B] (e : A ↪[L] B),
        Sentenceω.Realize σ A → Sentenceω.Realize σ B → Sentenceω.Realize φ A →
        Sentenceω.Realize φ B)
      ↔ ∃ θ : L.Sentenceω, IsExistential θ ∧ EquivModulo σ φ θ

theorem malitz_interpolation [L.IsRelational] (φ ψ : L.Sentenceω)
    (hψ : IsUniversal ψ) (h : Sentenceω.Entails φ ψ) :
    ∃ θ : L.Sentenceω, IsUniversal θ ∧
      θ.functionsIn ⊆ φ.functionsIn ∩ ψ.functionsIn ∧
      θ.relationsIn ⊆ φ.relationsIn ∩ ψ.relationsIn ∧
      Sentenceω.Entails φ θ ∧ Sentenceω.Entails θ ψ
```

Naming discipline, learned from #14's D1: because Malitz 1969 and Keisler 1971 are **not** verified
here, every statement, docstring, blueprint node, and release note must attribute these as *"Malitz's
interpolation theorem / relative preservation theorem, as stated in the expressive-efficiency notes,
Theorems 4.5/4.6"* — not as "Malitz 1969, Theorem N".  If the primary sources are obtained later, the
attribution can be sharpened; the mathematical content does not depend on it.  Also to freeze: `A ⊂ B`
in 4.6(1) is **substructure** (`↪[L]`, not elementary), and `σ ⊨ φ ↔ θ` is equivalence *in all models
of `σ`*, which needs its own definition (`EquivModulo`).

### D2 — the syntax classes: signed quantifier traversal, in a neutral module [proposed]

The source's `∀1`/`∃1` translate directly into the #14 pattern.  In our syntax the only primitive
quantifier is `all`, with `ex φ = (φ.not.all).not`, so an **existential quantifier is exactly an
`all` occurring negatively**.  Hence, with a sign-tracked traversal counting `all`-occurrences:

```lean
def quantifiersSigned : Bool → BoundedFormulaω L α n → Prop   -- "some `all` occurs with this sign"
IsUniversal φ   := ¬ quantifiersSigned false φ                -- no existential quantifier
IsExistential φ := ¬ quantifiersSigned true φ                 -- no universal quantifier
```

This matches all five source clauses: atomic ⇒ both classes (no `all` at all); negation exchanges
them (clause 2 — the sign flips); `iInf`/`iSup` preserve them and are *not* counted (clause 3 —
exactly our traversal, which recurses into components without touching the sign); `all` at positive
sign is universal, at negative sign existential (clauses 4/5 at `n = 1`).  **No negation-normal form
anywhere**, as in #14.

Placement, per the review and issue #15's own design note: a **neutral** module
`Lomega1omega/QuantifierClass.lean` (syntax) + `Lomega1omega/QuantifierSemantics.lean`
(preservation), beside `Polarity.lean`/`PolaritySemantics.lean`, depending only on `Syntax`/
`Semantics` — reusable by #16 (end extensions) and any future preservation theorem, and *not* inside
the interpolation development.

**What exists and what must be built** (audited, not assumed): the project has
`BoundedFormulaω.realize_equiv` (isomorphism transport) and `realize_congr_symbolsIn` (same carrier,
two structures) — and **nothing for embeddings**.  So milestone 2 owes a genuinely new lemma, the
quantifier analogue of #14's `realize_mono_of_signed`:

```lean
-- universal sentences pass to substructures; existential ones to extensions
realize_of_embedding_signed (e : A ↪[L] B) (φ) : (IsUniversal φ → Realize φ B → Realize φ A) ∧ …
```
proved by one induction with the **embedding fixed and the formula generalized**, the `imp` case
appealing to the dual direction — structurally the same trick as #14's ordered-pair generalization,
with "swap the structures" replaced by "swap the direction of transport".

### D3 — equality and function symbols, audited separately [proposed]

The source's scope for 4.5 is function-free, so **nothing about function symbols is inherited**.
Three separate questions, to be answered independently rather than by analogy with #14:

1. **Equality.**  Atomic formulas include `v = w`, and clause 1 puts every atomic formula in both
   classes, so equality is quantifier-neutral and imposes no constraint on `IsUniversal`.  Unlike
   #14 there is no ambiguity in the source and no clause to drop: the symbol condition in 4.5 is
   the plain Craig one, which our `functionsIn`/`relationsIn` machinery already expresses.  (Equality
   contributes to neither, exactly as in #14.)
2. **Function symbols in the relational core.**  `[L.IsRelational]` makes `functionsIn ⊆ ∩`
   vacuous; keep the conjunct for statement stability, as in #14's D3.
3. **Function symbols in the endpoints.**  Whether either endpoint extends beyond relational
   languages is D5's business, and the answer differs for the two theorems — which is exactly what
   the source's asymmetry (4.5 function-free, 4.6 any `τ`) predicts.

### D4 — does only the separator class change?  [**to be verified, not assumed**]

The hope, by analogy with #14: restrict the separating sentences to **universal** common-symbol
sentences and leave the consistency-property/Henkin kernel untouched.  Two things must be checked
*before* any assembly, and one of them is a genuine risk:

* **Good sign — the class is directional, exactly like polarity.**  `IsUniversal` is *not* closed
  under subformulas, but it is closed under the **sign-tracked** ones: if `φ.imp ψ` is universal then
  `ψ` is universal and `φ` is *existential*, so `φ.not` is universal.  That is precisely the shape of
  #14's `sentBndPol_imp_neg_left`/`sentBndPol_imp_right`, so the C1/C1′/C2/C3′/C4′ fields should port
  with the directional discipline already worked out — negation **exchanges** `IsUniversal` and
  `IsExistential`, and the right coordinate is the conjugate.
* **Genuine risk — the existential witness rule.**  The CP's `neg_all_witness` field fires on
  `φ.all.not ∈ S` and adds `(instConst c φ).not`.  But `φ.all.not` is *existential*, not universal:
  a side restricted to universal sentences cannot contain it, and dually a side restricted to
  existential sentences is where witnesses are needed.  So the universal restriction is **not**
  symmetric between the two coordinates, and the correct invariant is likely "left side universal,
  right side existential" (or a restriction imposed only on the *separator*, never on the sides).
  **Deciding which of those three shapes is correct is the Unit-2 stop/go gate**, and it must be
  settled by writing the C1 + witness fields for a candidate invariant *before* the 16-field
  assembly, exactly as #14's D7 did.

Until that gate passes, the claim "only the separator class changes" is a **hypothesis**, not a
finding.  #14's experience is evidence for it, not proof.

### D5 — relationalization is a stop/go gate, and it looks NEGATIVE for interpolation [proposed]

This is the audit's main new finding, and it must not be papered over by #14's success.

**Forward relationalization destroys `∀1`.**  In our layer, an atom's translation is *existentially
flattened*: `equalGraph t u = ∃y (termGraph t y ∧ termGraph u y)` and
`relGraph R ts = ∃ȳ (⋀ termGraph tᵢ yᵢ ∧ R(ȳ))` — `existsBlock`, i.e. negative-sign `all`s.  Worse,
the graph axioms are `∀x⃗ ∃y G_f(x⃗,y)` (totality), which is `∀2`, not `∀1`.  So even for a universal
`ψ`, both `Ax(F) ∧ ψʳᵉˡ` and `Ax(F) → ψʳᵉˡ` fail to be universal.  **The #14 wrapper route therefore
cannot transport the universal class**, and the source's function-free hypothesis on 4.5 is very
likely essential rather than incidental.  Recorded consequence: **do not claim an arbitrary-language
Malitz interpolation theorem**, and do not spend a unit attempting the wrapper.

**Back-translation, by contrast, preserves the quantifier class.**  `G_f(x⃗, y) ↦ f(x⃗) = y` is
quantifier-free, and back-translation is otherwise structural, so it maps `∃1` to `∃1` and `∀1` to
`∀1` (the signed twin of #14's Gate 3, and provable the same way).  That asymmetry is exactly what
the source's Theorem 4.6 "applies to any signature" needs: a *preservation* statement can be moved
to an arbitrary signature by relationalizing the **semantic** side (substructures and extensions
correspond under graph expansion) and back-translating the **syntactic** witness, whose existential
form survives.  So:

* arbitrary-signature **preservation** (Theorem 4.6): plausibly reachable — gate it on the
  back-translation quantifier-class lemma plus a substructure/extension correspondence for graph
  expansions;
* arbitrary-signature **interpolation** (Theorem 4.5): expected **unreachable** by this route, and
  not claimed.

### D6 — relational core first [proposed]

Prove `malitz_interpolation` for `[L.IsRelational]` (the source's own scope) and only then consider
any wrapper, and only for the preservation endpoint (D5).  No arbitrary-language interpolation
statement is to be written, even as a `sorry`-free-but-hypothetical shape.

### D7 — relative first, absolute derived [proposed]

State `malitz_relative_preservation` in the **mod-σ** form and derive the absolute Łoś–Tarski-style
theorem as the case `σ = ⊤`:

* absolute: `φ` preserved under extensions ↔ `φ` equivalent to an existential sentence;
* dual: `φ` preserved under substructures ↔ `φ` equivalent (mod `σ`) to a **universal** sentence —
  obtainable from the relative theorem applied to `φ.not` by the negation exchange of D2, so it
  costs one lemma, not a second development.

### Unit order (each a compile-gated commit)

0. `Lomega1omega/QuantifierClass.lean` — the signed quantifier traversal, `IsUniversal`,
   `IsExistential`, constructor equations, the negation **exchange**, closure under `iInf`/`iSup`,
   and the substitution/`instConst` calculus;
1. `Lomega1omega/QuantifierSemantics.lean` — the embedding-transfer gate (universal ⇒ preserved
   under substructures, existential ⇒ under extensions), the **first** acceptance gate, and the one
   piece the project does not already have in any form;
2. **stop/go**: the candidate universal-restricted separator/side invariant, with the C1 field and
   the `neg_all_witness` field only (D4);
3. the restricted side bounds and one-sided closures;
4. the paired family and consistency property;
5. `malitz_interpolation` for relational languages (D6);
6. `malitz_relative_preservation` (mod σ) + the absolute and dual corollaries (D7);
7. the arbitrary-signature preservation wrapper — **only** if D5's back-translation gate passes;
8. facade, blueprint, guards, docs, release.

## 3. Non-goals (recorded to prevent scope creep)

* **No set/theory-level preservation theorem** — refuted for `L_ω₁ω` by the source.
* **No two-sided quantifier-free form modulo σ** — the source says it fails relatively.
* **No arbitrary-language Malitz *interpolation*** (D5), and no claim that #14's wrapper transfers.
* **No `L_κω` for `κ > ω₁`** — Craig itself fails there.
* **No #16 end-extension work**; Units 0–1 are built to be reusable by it, nothing more.
* **No NNF datatype**, in either the syntax or the semantics layer.
* **No attribution to Malitz 1969 / Keisler 1971 as verified sources** until they are read (D1).
