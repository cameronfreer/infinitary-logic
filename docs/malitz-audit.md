# Malitz universal interpolation and relative preservation (#15): statement-and-interface audit (v2, FROZEN)

Pre-implementation audit for issue #15, in the pattern of `docs/craig-audit.md`,
`docs/wellordering-audit.md`, `docs/lopez-escobar-hard-audit.md`, and `docs/lyndon-audit.md`.
**No Lean before the D-points are signed off.**

Primary source read directly: Harrison-Trainor and Kretschmer, *Infinitary Logic Has No Expressive
Efficiency Over Finitary Logic* ([notes](https://homepages.math.uic.edu/~mht/papers/expressive-efficiency.pdf),
arXiv 2209.05615), §2 for the `∀n`/`∃n` hierarchy and §4.2.2 for Theorems 4.5–4.7, checked
2026-07-26.  These state and attribute Malitz's results ([Mal69] = *Universal classes in infinitary
languages*, Duke Math. J. 36 (1969) 621–630) and note that the relative form appears in Keisler
[Kei71].  **Malitz 1969 and Keisler 1971 themselves are not verified here** — see D1 for exactly
what that costs.

Status: **v2, FROZEN per review 2026-07-26.**  Changes from v1, all load-bearing: the preservation
statements are aligned with the repository's **nonempty** semantics and `EquivModulo` is pinned
(§D1); the Unit-1 acceptance gate is **valuation-aware**, over bounded formulas and tuples, with
sentence preservation a corollary (§D2); the Unit-2 candidate invariants are corrected — "left
universal" is **impossible**, since the left root is the arbitrary antecedent — and the decisive
spike becomes the **two-sided C7 gate**, before C1 and before any family assembly (§D4); and the
Unit-7 wrapper gate is strengthened to a four-obligation square, with the wrapper described as a
**candidate** deliverable rather than an expected consequence (§D5).

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

### D1 — freeze the statements before any Lean predicate [FROZEN]

Two endpoints, in this order (D7), stated over the repository's model class — `Type`-level carriers
that are **nonempty**, matching `Sentenceω.Entails`, which quantifies over `[Nonempty M]`.  Getting
this wrong would have the two sides of the equivalence range over different model classes:

```lean
/-- Equivalence of two sentences in all (nonempty) models of a background sentence. -/
def EquivModulo (σ φ θ : L.Sentenceω) : Prop :=
  ∀ (M : Type) [L.Structure M] [Nonempty M],
    Sentenceω.Realize σ M → (Sentenceω.Realize φ M ↔ Sentenceω.Realize θ M)

/-- Preservation upward along substructure embeddings, among models of `σ`. -/
def PreservedUnderExtensions (σ φ : L.Sentenceω) : Prop :=
  ∀ (A B : Type) [L.Structure A] [Nonempty A] [L.Structure B] [Nonempty B] (e : A ↪[L] B),
    Sentenceω.Realize σ A → Sentenceω.Realize σ B → Sentenceω.Realize φ A → Sentenceω.Realize φ B

theorem malitz_relative_preservation (σ φ : L.Sentenceω) :
    PreservedUnderExtensions σ φ ↔ ∃ θ : L.Sentenceω, IsExistential θ ∧ EquivModulo σ φ θ

theorem malitz_interpolation [L.IsRelational] (φ ψ : L.Sentenceω)
    (hψ : IsUniversal ψ) (h : Sentenceω.Entails φ ψ) :
    ∃ θ : L.Sentenceω, IsUniversal θ ∧
      θ.functionsIn ⊆ φ.functionsIn ∩ ψ.functionsIn ∧
      θ.relationsIn ⊆ φ.relationsIn ∩ ψ.relationsIn ∧
      Sentenceω.Entails φ θ ∧ Sentenceω.Entails θ ψ
```

Naming discipline, learned from #14's D1: because Malitz 1969 and Keisler 1971 are **not** verified
here, every statement, docstring, blueprint node, and release note must attribute these as *"Malitz's
interpolation / relative preservation theorem, as stated in Harrison-Trainor–Kretschmer, Theorems
4.5/4.6"* — not as "Malitz 1969, Theorem N".  If the primary sources are obtained later the
attribution can be sharpened; the mathematical content does not depend on it.  Also frozen: `A ⊂ B`
in 4.6(1) is **substructure** (`↪[L]`, not elementary), and `σ ⊨ φ ↔ θ` is `EquivModulo` above.

### D2 — the syntax classes and the valuation-aware semantic gate [FROZEN]

The source's `∀1`/`∃1` translate directly into the #14 pattern.  In our syntax the only primitive
quantifier is `all`, with `ex φ = (φ.not.all).not`, so an **existential quantifier is exactly an
`all` occurring negatively**.  One `Bool`-parameterised recursion carries both classes, so the
mutual dependence (negation exchanges them) is definitional rather than an extra induction:

```lean
/-- `universalSigned true` is "is universal", `universalSigned false` is "is existential". -/
def universalSigned : Bool → L.BoundedFormulaω α n → Prop
  | _, .falsum    => True
  | _, .equal _ _ => True
  | _, .rel _ _   => True
  | s, .imp φ ψ   => universalSigned (!s) φ ∧ universalSigned s ψ   -- antecedent flips
  | s, .all φ     => s = true ∧ universalSigned s φ                 -- a `∀` is universal only
  | s, .iSup φs   => ∀ i, universalSigned s (φs i)                  -- not counted (clause 3)
  | s, .iInf φs   => ∀ i, universalSigned s (φs i)

abbrev IsUniversal   (φ) := universalSigned true φ
abbrev IsExistential (φ) := universalSigned false φ
```

This matches all five source clauses: atomic ⇒ both classes; negation exchanges them (clause 2, via
the `imp` flip and `not = imp _ ⊥`); `iInf`/`iSup` preserve them and are **not** counted (clause 3);
`all` is universal-only (clauses 4/5 at `n = 1`).  **No negation-normal form anywhere**, as in #14.

**Unit-0 acceptance equations** (each must be a stated lemma, not left to unfolding):

```lean
IsUniversal (φ.imp ψ)   ↔ IsExistential φ ∧ IsUniversal ψ
IsExistential (φ.imp ψ) ↔ IsUniversal φ ∧ IsExistential ψ
IsUniversal φ.not       ↔ IsExistential φ
IsExistential φ.not     ↔ IsUniversal φ
IsUniversal φ.all       ↔ IsUniversal φ
¬ IsExistential φ.all
```

plus the `iInf`/`iSup` componentwise equations, `⊤`/`⊥`/atoms in both classes, and the
substitution/`instConst`/`relabel`/`castLE` calculus (the quantifier analogue of Unit 0 in #14).

**Unit-1 acceptance gate — valuation-aware.**  The gate must be stated for **bounded** formulas and
tuples, transported along the embedding, with sentence preservation a corollary rather than the
primitive:

```lean
theorem realize_of_embedding_signed (e : A ↪[L] B) :
    ∀ {n : ℕ} (φ : L.BoundedFormulaω α n) (v : α → A) (xs : Fin n → A),
      (IsUniversal φ   → φ.Realize (e ∘ v) (e ∘ xs) → φ.Realize v xs) ∧
      (IsExistential φ → φ.Realize v xs → φ.Realize (e ∘ v) (e ∘ xs))
```

One induction, both directions at once (the `imp` case needs the other direction, exactly as #14's
monotonicity gate needed the swapped structure pair — here "swap the structures" becomes "swap the
direction of transport").  The `all` case is where the two directions differ: downward transport
instantiates at `e x`, upward transport is **blocked** for a positive `∀`, which is precisely why
`IsExistential (φ.all)` is false.  Corollaries: universal sentences pass to substructures,
existential sentences to extensions, both with the `[Nonempty]` hypotheses of D1.

**What exists and what must be built** (audited, not assumed): the project has
`BoundedFormulaω.realize_equiv` (isomorphism transport) and `realize_congr_symbolsIn` (same carrier,
two structures) — and **nothing for embeddings**.  So Unit 1 is genuinely new work.

Placement, per the review and issue #15's own design note: neutral modules
`Lomega1omega/QuantifierClass.lean` (syntax) and `Lomega1omega/QuantifierSemantics.lean`
(preservation), beside `Polarity.lean`/`PolaritySemantics.lean`, depending only on `Syntax`/
`Semantics` — reusable by #16 (end extensions) and any future preservation theorem, and *not* inside
the interpolation development.

### D3 — equality and function symbols, audited separately [FROZEN]

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

### D4 — does only the separator class change?  [**to be decided by the two-sided C7 spike**]

The hope, by analogy with #14: restrict the *separating* sentences to **universal** common-symbol
sentences and leave the consistency-property/Henkin kernel untouched.  What the audit can settle now,
and what it cannot:

**Settled — the class is directional, exactly like polarity.**  `IsUniversal` is not closed under
subformulas but *is* closed under the **sign-tracked** ones: from `φ.imp ψ` universal one gets `ψ`
universal and `φ` **existential**, hence `φ.not` universal.  That is #14's
`sentBndPol_imp_neg_left`/`_imp_right` discipline verbatim, so if a side restriction is used at all,
C1/C1′/C2/C3′/C4′ should port with the directional rules already worked out.

**Settled — "left universal" is impossible.**  In the interpolation argument the left root *is* the
arbitrary antecedent `φ`, on which the theorem assumes nothing; only the right root `ψ` is universal
(and enters as `ψ.not`, hence existential).  So `Γ` can never be universally restricted.  The viable
candidate invariants are therefore:

1. `Γ` **unrestricted**, `Δ` existential, separator universal;
2. a restriction on the **separator only**, with both sides unrestricted;
3. a richer asymmetric or two-class invariant (e.g. tracking a universal *and* an existential bound
   per coordinate).

**Not settled — and this is the decisive gate.**  The obstruction is sharper than v1 said, and it
lives in the **fresh-witness (C7) machinery**, not in C1:

* the existing **left**-coordinate C7 abstracts the separator with `genEx` (`insepAt_witness_of_
  insepAt_genEx`, `lyndonInsepAt_witness_of_genEx`): it replaces `σ` by `∃x σ(x)`, which turns a
  **universal separator into an existential one** — i.e. it destroys exactly the property the
  separator class is supposed to have;
* the **right**-coordinate direction may instead admit a *new* **universal** abstraction using a
  `genAll` (∀-generalisation of a fresh constant), because the freshness hypothesis is available on
  the opposite side.  The project has `genEx` (`ConstantElimination.lean`) but **no `genAll`**, so
  this is new work: `genAll j ρ := ((ρ.abstractConst j).relabel …).all`, with its own realization
  lemma and support/occurrence calculus.

**Unit 2 is therefore the two C7 toy gates and nothing else** — prove (or refute) the left-coordinate
universal-separator abstraction and the right-coordinate `genAll` abstraction, *before* C1 and before
any family assembly.  If the left gate fails, that failure is precisely the proof that candidate 2
(separator-only closure) cannot work, and it selects candidate 1 or 3 on evidence rather than by
analogy.  Only after that does the side-bound suite (Unit 3) have a determinate shape.

Until this gate reports, "only the separator class changes" remains a **hypothesis**; #14's
experience is evidence for it, not proof.

### D5 — relationalization is a stop/go gate, NEGATIVE for interpolation [FROZEN]

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
`∀1` (the signed twin of #14's Gate 3, provable the same way).  That asymmetry is what the source's
"applies to any signature `τ`" needs for Theorem 4.6.

**But quantifier-class preservation is necessary, not sufficient.**  Before any arbitrary-signature
*preservation* result is promised, four further obligations must be audited **and compile-gated**,
because the wrapper has to move a *semantic* hypothesis (preservation along embeddings) between the
two languages, not just a syntactic witness:

1. **Reconstruction of the function structure** — from a graph-language model satisfying `Ax(F)`,
   recover an `L`-structure (this exists: `reconstructStructure`, used by Craig), and know exactly
   which `F` is needed for the sentences at hand;
2. **Correspondence of substructures/embeddings** through graph expansion *and* reconstruction: an
   `L`-embedding `A ↪[L] B` must give a graph-language embedding of the expansions, and conversely a
   graph-language embedding between models of `Ax(F)` must reconstruct to an `L`-embedding.  Neither
   direction exists in the project today;
3. **Transport of the background theory** — both `A ⊨ σ` and `B ⊨ σ` must move to the graph side and
   back, for the *same* `σʳᵉˡ`, which interacts with obligation 1's choice of `F`;
4. **Transport of the existential witness sentence** back to `L`, with its `IsExistential` shape
   intact (this is the benign direction, by the back-translation class lemma).

Until that square closes, the arbitrary-signature preservation wrapper is a **candidate deliverable,
not an expected consequence**, and it is scheduled as Unit 7 *conditional* on the gate.  The
arbitrary-signature **interpolation** statement remains not claimed at all (see above).

### D6 — relational core first [FROZEN]

Prove `malitz_interpolation` for `[L.IsRelational]` (the source's own scope) and only then consider
any wrapper, and only for the preservation endpoint (D5).  No arbitrary-language interpolation
statement is to be written, even as a `sorry`-free-but-hypothetical shape.

### D7 — relative first, absolute derived [FROZEN]

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
2. **stop/go — the two C7 toy gates only** (D4): the left-coordinate universal-separator
   abstraction (expected to fail) and the right-coordinate `genAll` abstraction (new machinery),
   before C1 and before any family assembly;
3. the restricted side bounds and one-sided closures;
4. the paired family and consistency property;
5. `malitz_interpolation` for relational languages (D6);
6. `malitz_relative_preservation` (mod σ) + the absolute and dual corollaries (D7);
7. the arbitrary-signature preservation wrapper — **candidate only**, and only if all four
   obligations of D5's square close;
8. facade, blueprint, guards, docs, release.

## 3. Non-goals (recorded to prevent scope creep)

* **No set/theory-level preservation theorem** — refuted for `L_ω₁ω` by the source.
* **No two-sided quantifier-free form modulo σ** — the source says it fails relatively.
* **No arbitrary-language Malitz *interpolation*** (D5), and no claim that #14's wrapper transfers.
* **No `L_κω` for `κ > ω₁`** — Craig itself fails there.
* **No #16 end-extension work**; Units 0–1 are built to be reusable by it, nothing more.
* **No NNF datatype**, in either the syntax or the semantics layer.
* **No attribution to Malitz 1969 / Keisler 1971 as verified sources** until they are read (D1).
