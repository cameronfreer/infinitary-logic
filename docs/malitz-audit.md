# Malitz universal interpolation and relative preservation (#15): statement-and-interface audit (v6)

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

Status: **v6, 2026-07-26.**  Amends v5 with the next session's deliverable contract (§D8: the
source-reconstruction document must pin the fresh-witness invariant *and* the root residue-removal
mechanism; no C0–C6 work until both are explicit) and records in §1 exactly what the
Harrison-Trainor–Kretschmer paper does and does not supply.

Status: **v5, 2026-07-26.**  §D4 is resolved *for the existing C7 strategies* by the Unit-2 spike;
§D4.5 records the root-to-embedding consumer gate, which **fails**, so the source unit order is
restored; **Units 0–2 are frozen COMPLETE** and §D8 makes Unit 3 an *audit* gate — source
reconstruction and a frozen certificate design before any Lean.  All other D-points remain frozen as
in v2.

Status (v2): **FROZEN per review 2026-07-26.**  Changes from v1, all load-bearing: the preservation
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

**What this source is, and is not, for #15.**  The paper's own theorem is that infinitary logic has
no expressive efficiency over finitary logic — roughly, a finitary formula equivalent modulo a
finitary theory to an infinitary formula with `n` quantifier alternations is already equivalent to a
finitary formula with `n` alternations.  Theorems 4.5 and 4.6 enter it as **cited ingredients**, not
as results it proves.  So the paper is authoritative for exactly three things: it fixes the
statements and their scopes (function-free for 4.5, arbitrary signature for 4.6); it confirms the
`∀1`/`∃1` counting we formalized in Unit 0, in which infinite conjunctions and disjunctions are not
quantifiers; and it fixes the dependency direction, presenting 4.6 as a consequence of 4.5.  It
supplies **no proof**, hence nothing about the candidate-3 construction — for the shared-vocabulary
C7 architecture the sources are Malitz's original, Keisler's presentation, or a new proof tailored
to this repository (§D8).

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

### D4 — does only the separator class change?  [**resolved for the existing C7 strategies**; candidate 3 open]

The hope, by analogy with #14: restrict the *separating* sentences to **universal** common-symbol
sentences and leave the consistency-property/Henkin kernel untouched.

**Settled — the class is directional, exactly like polarity.**  `IsUniversal` is not closed under
subformulas but *is* closed under the **sign-tracked** ones: from `φ.imp ψ` universal one gets `ψ`
universal and `φ` **existential**, hence `φ.not` universal.  That is #14's
`sentBndPol_imp_neg_left`/`_imp_right` discipline verbatim, so if a side restriction is used at all,
C1/C1′/C2/C3′/C4′ should port with the directional rules already worked out.

**Settled — "left universal" is impossible.**  In the interpolation argument the left root *is* the
arbitrary antecedent `φ`, on which the theorem assumes nothing; only the right root `ψ` is universal
(and enters as `ψ.not`, hence existential).  So `Γ` can never be universally restricted.  The
candidate invariants were therefore:

1. `Γ` **unrestricted**, `Δ` existential, separator universal;
2. a restriction on the **separator only**, with both sides unrestricted;
3. a richer asymmetric or two-class invariant.

**The spike, and what it measured.**  Unit 2 is the two C7 fresh-witness gates and nothing else —
`InfinitaryLogic/Methods/Interpolation/MalitzC7Spike.lean`, over
`MalitzInsepAt F R A Γ Δ` = `InsepAt` with the separator additionally `IsUniversal`.

*Right trigger (witness on the `Δ` side) — **clean, unconditional**.*  `genAll`, the
`∀`-generalization of a fresh constant, is new machinery (the project had only `genEx`).  It is
class-preserving —

```lean
isUniversal_genAll : IsUniversal (genAll j ρ) ↔ IsUniversal ρ
```

— because `all` is admissible at the universal sign, and constant abstraction and `relabel` do not
move the class.  With its two acceptance sequents (`entails_genAll_of_entails`, which unlike
`genEx`'s `Γ`-side sequent genuinely needs freshness because `∀`-introduction is not weakening, and
`entails_not_genAll_of_entails_not`), `malitzInsepAt_witness_of_genAll` holds with **no side
conditions beyond freshness** — exactly the shape of the existing Craig/Lyndon gates.

*Left trigger (witness on the `Γ` side) — the `genEx` route fails **syntactically**, and the
replacement closes only outside the shared vocabulary.*  `genEx c σ` is `∃x σ(x)`, hence `Σ2` for
universal `σ`; `not_isUniversal_genEx` records this as a fact about the **construction**, not as a
failure of the closure.  The replacement is the finite-existential-side conjunction: with `Δ`
existential (and countable), `δΔ := ⋀ Δ` is existential, so `¬δΔ` is universal, `Δ ⊨ ¬¬δΔ` is
trivial, and `Γ, ∃x φ(x) ⊨ ¬δΔ` because a model of both would reinterpret the fresh `c` at the
existential witness, keeping `Γ` and `Δ` standing and producing `σ(c)` and `¬σ(c)` at once.  This is
formalized as `malitzInsepAt_witness_of_existentialDelta` and it **compiles** — but with three
hypotheses about `Δ`:

```
hΔA : ∀ δ ∈ Δ, sentenceJConsts δ ⊆ ↑A       -- free: PairedInsepFamilyMem already carries it
hΔF : ∀ δ ∈ Δ, δ.baseFunctionsIn ⊆ F        -- NOT available
hΔR : ∀ δ ∈ Δ, δ.baseRelationsIn ⊆ R        -- NOT available
```

The two symbol bounds are the obstruction.  In the interpolation family the separator budget is the
**shared** vocabulary `(F₁ ∩ F₂, R₁ ∩ R₂)` while `Δ ⊆ SentBnd F₂ R₂`, so `¬δΔ` is a legal separator
only when `F₂ ⊆ F₁` and `R₂ ⊆ R₁`.  That is not a formalization artifact: a separator built out of
`Δ` itself is exactly what the shared-vocabulary condition forbids, and forbidding it is what makes
interpolation a theorem rather than a triviality.

**Verdict, at its actual scope.**  Candidate 1's *semantic* content is confirmed on both sides —
`Γ` unrestricted, `Δ` existential, separator universal is the right asymmetry, and it matches the
source theorem's own shape (arbitrary antecedent, universal consequent).  What is settled is:

* the **right** C7 gate holds unconditionally, and `genAll` is permanent, architecture-independent
  infrastructure;
* the **left** C7 gate holds only when the separator's symbol budget already contains `Δ`;
* consequently **candidate 2 is ruled out for this paired-family closure argument** — it is the
  gate, not merely the `genEx` construction, that fails.  This is not a mathematical refutation of a
  separator-only restriction in every possible architecture.

D4 is therefore resolved **for the existing C7 strategies**.  Candidate 3 — a richer asymmetric or
two-class invariant, or a different architecture altogether — is untouched by the spike and remains
the live option for Theorem 4.5.

Whether the residual `hΔF`/`hΔR` obligation can be met by a *different consumer* rather than a
different invariant is the subject of §D4.5.

### D4.5 — the root-to-embedding consumer gate [**FAILS; source order restored**]

Unit 2 established that candidate 1 closes when `Δ` already lies inside the separator's symbol
budget.  Before any closure suite is built on that, the audit owes an account of a *consumer* that
supplies that budget without destroying the theorem's content.  Two things make this non-optional:

* widening `F`, `R` to the full symbol sets makes the C7 bounds trivial but removes **all**
  interpolation content, so it is not by itself a justification for anything;
* the repository's Henkin/quotient endpoint produces **one** model.  `exists_lyndon_paired_model`
  (and its Craig twin) has the shape `∃ (M : Type) (_ : L[[ℕ]].Structure M) (_ : Nonempty M),
  Realize rL M ∧ Realize rR M`.  But failure of `PreservedUnderExtensions σ φ` needs **two**
  structures and an embedding.

**The acceptance statement** (the consumer obligation, recorded verbatim so it cannot be quietly
weakened):

```lean
theorem exists_extension_counterexample_of_no_existential_equiv
    (hno : ¬ ∃ θ, IsExistential θ ∧ EquivModulo σ φ θ) :
    ∃ A B (_ : L.Structure A) (_ : L.Structure B)
      (_ : Nonempty A) (_ : Nonempty B) (e : A ↪[L] B),
      Realize σ A ∧ Realize σ B ∧ Realize φ A ∧ ¬ Realize φ B
```

**The five questions, answered for the only encoding the machinery admits.**

1. *Language.*  Since completion yields a single model, the pair must be **tagged inside it**:
   `L⁺ := L` plus one fresh unary relation symbol `U`.  No two-model or amalgamation endpoint exists
   anywhere in the tree.
2. *Roots.*  `rL := Ax(U) ∧ (σ ∧ φ)^U` — the `U`-relativization of the substructure's theory,
   together with the axioms making `U` carve out an `L`-substructure — and `rR := σ ∧ ¬φ`.
3. *Where `A`, `B`, `e` live.*  `B` is the produced model's `L`-reduct, `A` is the substructure
   carried by `U^M`, and `e` is `Substructure.subtype`.
4. *One tagged model or two quotient models.*  **One tagged model.**  The quotient term model is
   built once; the pair is read off it.
5. *Which theorem extracts the embedding.*  **None exists.**  It would require, all new: the
   one-predicate expansion; a relativization operator `φ ↦ φ^U` on `BoundedFormulaω` with its
   semantic lemma (`Realize (φ^U) M ↔ Realize φ (U^M)`); the closure axioms `Ax(U)` — nonemptiness
   only in the relational case, but `∀x⃗ ∃y G_f(x⃗,y)`-style totality otherwise, which is `∀2`, the
   same obstruction D5 found; and the extraction theorem itself.

**Why the square does not close — and it is not the missing machinery.**  The encoding above
*does* supply the vocabulary hypothesis: with the relativized root on the `Γ` coordinate,
`F₂ = L ⊆ F₁ = L ∪ {U}`, so `hΔF`/`hΔR` hold, and the budget `F₁ ∩ F₂ = L` is a genuine restriction
(it is exactly "the separator does not mention `U`"), not a full budget.  But candidate 1 also needs
`hΔex`: **`Δ` existential**.  In this encoding the `Δ` root is `σ ∧ ¬φ` for arbitrary `σ`, `φ` —
whichever way the two roots are assigned to the coordinates, the plain root is an arbitrary sentence
— so `hΔex` fails at the root, before any closure step runs.

The two hypotheses are supplied by **disjoint settings**:

| setting | `hΔex` (`Δ` existential) | `hΔF`/`hΔR` (`Δ` inside the budget) |
| --- | --- | --- |
| Theorem 4.5, interpolation | ✅ — the right root is `ψ.not`, existential *because* `ψ` is universal | ❌ — the budget is the genuinely shared `F₁ ∩ F₂` |
| relativized preservation | ❌ — the right root is an arbitrary `σ ∧ ¬φ` | ✅ — `F₂ = L ⊆ F₁ = L ∪ {U}` |

`hΔex` is not incidental: it *is* Theorem 4.5's universality hypothesis on `ψ`, which is why the
one setting that provides it is the one with a real shared-vocabulary condition.

**Decision.**  The square cannot be frozen, so the source order is **restored**: solve the
shared-vocabulary candidate-3 architecture for Theorem 4.5, then derive Theorem 4.6 from it as the
source does (Harrison-Trainor–Kretschmer present 4.6 as a consequence of 4.5, not as an independent
application of a Henkin family).  The relativization encoding above is *not* discarded — it is the
natural consumer for 4.6 once 4.5 exists, and §D4.5 is the specification it must meet.

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

### D8 — candidate 3: the Unit-3 **audit** gate [**Task 1 DONE** — see `docs/malitz-source-reconstruction.md`]

**Outcome (2026-07-26).**  The construction was found: Feferman's *many-sorted* interpolation
theorem, presented with a full consistency-property proof in Väänänen, *Interpolation in model
theory* ([arXiv 2507.19097](https://arxiv.org/pdf/2507.19097)), which specializes to Theorem 4.5 and
from which Malitz's preservation theorem is derived by a two-sorted `EXT` encoding.  Both §D8
deliverables are identified:

* **fresh-witness invariant** — the separator may mention Henkin constants, and each constant's sort
  is charged into **both** the universal and the existential budget, so existentially generalizing a
  witness constant is budget-neutral.  Our `MalitzInsepAt` restricted the class *absolutely* and
  charged nothing, which is exactly why `genEx` could not be paid for;
* **root residue elimination** — **none is needed**: the flow is inverted.  The root pair `{φ, ¬ψ}`
  is where the argument starts and is constant-free; (⋆) is a hypothesis at the root propagated
  downward to a model, not a conclusion extracted at the end.

In the single-sorted Malitz case the budget collapses: `Ex′(θ) ⊆ Un({¬ψ}) = Ex(ψ) = ∅` forces the
separator to be universal **and constant-free at every stage**, so both C7 steps become the identity
and the constant-abstraction apparatus is unused.  The abandonment clause below is **not** triggered
— the construction is a consistency-property argument of the shape this repository already supports.

**Task 2 frozen by review (2026-07-26): the single-set / canonical-projection invariant.**  Väänänen's
`S₁`, `S₂` are the *side-language projections of one finite set* `S`, so a shared sentence lies in
**both**; an arbitrary pair `(Γ, Δ)` is not a faithful substitute, and dropping a constant-free
separator class into the old pair shell **breaks C0** (`Γ = {P(c)}`, `Δ = {¬P(c)}` with `P` shared has
no constant-free universal separator, while in the projection representation each projection is
inconsistent and `⊥` separates).  The frozen family is

```lean
side F R S      := S ∩ SentBnd F R
FefermanMem S   := S.Finite ∧ S ⊆ GenU … ∧ S = side F₁ R₁ S ∪ side F₂ R₂ S
                     ∧ no constant-free universal separator of side F₁ R₁ S and side F₂ R₂ S
```

with the support parameter `A` **gone**, replaced by `sentenceJConsts σ = ∅`.  Both C7
transformations are the identity on the separator, and the root-to-interpolant equation is trivial.

**Unit 3's order, frozen:** (1) canonical side projections; (2) the shared-overlap/C0 toy theorem;
(3) the projection-aware left **and** right C7 identity theorems; (4) only then audit the remaining
consistency fields.  The C7 gates are stated by extending `S`, not `Γ`.

Two precision corrections carried into the reconstruction: the Craig/Feferman contrast is **not** an
inverted flow — both start at the root and extend a consistency condition downward; the difference is
that Feferman never permits separator support, whereas Craig permits budgeted support and discharges
it at the empty root budget.  And Väänänen's Theorem 23 is the **absolute** submodel/universal
preservation theorem, not the relative mod-`σ` Theorem 4.6; its `EXT` encoding also uses cross-sort
equality with no repository representation, so preservation is a **later** gate with its own audit.

---

The gate as originally frozen:

Unit 3 is **not a Lean unit**.  §D4.5 established that the paired-family route cannot be rescued by
choosing a different consumer, so the next step is to find out what Malitz's proof actually does
before any invariant is designed to fit our machinery.

**Task 1 — read the source construction.**  Harrison-Trainor–Kretschmer state and attribute; they do
not reproduce the proof.  Read Malitz [Mal69] itself, or Keisler's Malitz-interpolation chapter
[Kei71].  The Berkeley Logic Library (<https://logic-library.berkeley.edu/>) lists Malitz's
dissertation, which may expose the original construction.  Until one of these is read, every claim
below about "the proof" is a hypothesis.

**The next session's only deliverable is a source-reconstruction document**, and its decisive content
is **not a broad proof summary**.  Two things must come out explicit, and nothing downstream starts
until both do:

1. **the exact invariant maintained at the fresh-witness step** — what the proof carries across the
   step that our `MalitzInsepAt` could not; and
2. **the mechanism that removes all nonshared residue at the root** — how the final object is forced
   into the shared vocabulary.

These are the two halves of the acceptance question below, in the order the proof must answer them.
A reconstruction that describes the argument's shape without pinning both is not a passing gate.

**Task 2 — freeze the replacement for `MalitzInsepAt`, in full, before coding.**  Four items, none
of them optional:

1. the **certificate shape** — what a separator *is* under candidate 3 (a single sentence, a pair, a
   sentence plus a side-language residue, …);
2. the **shared-symbol invariant** it carries;
3. **both** C7 transformations, left and right, stated on that certificate;
4. the **root-to-interpolant equation** — how a support-`∅` certificate becomes the interpolant.

**Task 3 — the left-C7 toy theorem must compile before any of C0–C6 is ported.**  This is the same
discipline that made Unit 2 informative: the known-hard step first, in isolation.  **No C0–C6 work
begins while either half of Task 1's deliverable is still implicit.**

**Task 4 — an explicit abandonment clause.**  If the source proof turns out to run on universal
consequences, diagrams, embeddings, or tableaux rather than a two-sided inseparability family, then
**abandon the paired-family route** and build that argument instead.  Do not force the source's
proof through a richer predicate merely because the Craig/Lyndon machinery exists.

**The acceptance question for candidate 3** (frozen wording):

> Can a separator certificate retain a **shared universal core** while carrying **nonshared
> existential residue**, and does the residue **disappear at the root**?

Both halves are required.  Preserving such a certificate through C7 is *not* sufficient: the root
gate must extract an actual shared universal sentence, with **no residual side-language formula**
left over.  A candidate-3 design that answers only the first half is a failed design, and this
audit's Unit-2 experience is the reason to say so in advance — the left C7 step is exactly where a
residue would be introduced, and the root is exactly where it must be gone.

### Status of Units 0–2 [**COMPLETE, frozen 2026-07-26**]

| unit | deliverable | commit | outcome |
| --- | --- | --- | --- |
| 0 | `Lomega1omega/QuantifierClass.lean` — signed `∀₁`/`∃₁` traversal, six acceptance equations, `castLE`/`relabel`/`subst` calculus | `9150019` | complete |
| 1 | `Lomega1omega/QuantifierSemantics.lean` — `realize_of_embedding_signed`, valuation-aware, both directions in one induction, sentence corollaries | `212663f` | complete |
| 2 | `Methods/Interpolation/MalitzC7Spike.lean` — `MalitzInsepAt` + the two C7 gates | `50c0627` | **stop/go reported**; see §D4/§D4.5 |
| 2 (cleanup) | `Methods/Interpolation/ConstantGeneralization.lean` — neutral `genAll` layer, class of constant abstraction, `Theoryω.conjunction` bounds | `86efb2c` | complete, reusable by #16 |

Units 0, 1 and the `ConstantGeneralization` layer are **architecture-independent**: they survive any
candidate-3 design unchanged.  `MalitzC7Spike.lean` is retained as the record of what was measured,
not as a foundation to build on.

### Unit order (each a compile-gated commit)

0. `Lomega1omega/QuantifierClass.lean` — the signed quantifier traversal, `IsUniversal`,
   `IsExistential`, constructor equations, the negation **exchange**, closure under `iInf`/`iSup`,
   and the substitution/`instConst` calculus;
1. `Lomega1omega/QuantifierSemantics.lean` — the embedding-transfer gate (universal ⇒ preserved
   under substructures, existential ⇒ under extensions), the **first** acceptance gate, and the one
   piece the project does not already have in any form;
2. **stop/go — the two C7 gates only** (D4): `genAll` plus the right-coordinate abstraction, and
   the left-coordinate finite-existential-side conjunction, before C1 and before any family
   assembly.  **DONE**, verdict in D4;
3. **candidate 3 — an AUDIT gate, not a Lean unit** (§D8): source reconstruction, then a frozen
   certificate design, then the left-C7 toy theorem in isolation, with an explicit clause for
   abandoning the paired-family route if the source proof is not of that shape;
4. the restricted side bounds and one-sided closures, once candidate 3 fixes the invariant;
5. the paired family and consistency property;
6. `malitz_interpolation` for relational languages (D6);
7. `malitz_relative_preservation` (mod σ) + the absolute and dual corollaries (D7), **derived from
   the interpolation theorem as in the source**, with §D4.5's relativization encoding as the
   consumer;
8. the arbitrary-signature preservation wrapper — **candidate only**, and only if all four
   obligations of D5's square close;
9. facade, blueprint, guards, docs, release.

## 3. Non-goals (recorded to prevent scope creep)

* **No set/theory-level preservation theorem** — refuted for `L_ω₁ω` by the source.
* **No two-sided quantifier-free form modulo σ** — the source says it fails relatively.
* **No arbitrary-language Malitz *interpolation*** (D5), and no claim that #14's wrapper transfers.
* **No `L_κω` for `κ > ω₁`** — Craig itself fails there.
* **No #16 end-extension work**; Units 0–1 are built to be reusable by it, nothing more.
* **No NNF datatype**, in either the syntax or the semantics layer.
* **No attribution to Malitz 1969 / Keisler 1971 as verified sources** until they are read (D1).
