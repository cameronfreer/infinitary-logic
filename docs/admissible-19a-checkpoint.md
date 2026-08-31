# The #19A representation checkpoint

Companion to `docs/admissible-interface-contract.md` (issue #18, whose §6 lists the items deferred
here). That contract froze the *fragment* interface; this one records what the #19A source/design
spike established about **representation** — the coding carrier, the sentence/theory/Σ layers, and
what the honest HF instance requires.

Everything below marked **established** was checked in Lean. Everything marked **placeholder** is a
known gap, named so that it cannot be mistaken for settled.

---

## 0. What is settled, and what is not

| Claim | Status |
|---|---|
| `L.Sentenceω` cannot be encoded into `ℕ` | **established** (theorem) |
| HF must encode the *finitary fragment*, not `Sentenceω` | **established** |
| One ambient `Element` with typed kinds, not separate sorts | **established** |
| Σ-definition codes carry *sentence codes*, giving functionality for free | **established** |
| Fragment containment is derivable from Σ-definability + adequacy | **established** |
| "c.e." must mean `Nat.Partrec`, not an unrestricted `W` | **established** |
| The sentence coding must be stored data, not an `Encodable` instance | **established** |
| The `A`-finite / theory-code layer | **established** — derived from ambient membership, §6(b) |
| HF `A`-finiteness is **not** globally ordinary finiteness | **established** (theorem) — §6(b) |
| Pairing and union carry specification laws | **established** — §6(c) |
| `Sigma1` is numbering-independent | **established** — via a second layer, §6(a) |
| KP beyond pairing and union | **deferred** — pending the source audit, §6(c) |

---

## 1. The falsification: `Sentenceω` is uncountable

**`HFSigmaData` carrying `encode : L.Sentenceω → ℕ` is uninstantiable.** For any language with two
distinct sentences, `fun s : Set ℕ => iInf (fun k => if k ∈ s then φ₁ else φ₀)` is injective by
constructor injectivity, so `Set ℕ` embeds in `L.Sentenceω` and Cantor finishes it.

Countably branching syntax already contains a distinct sentence per set of naturals, so **countability
of the language does not help** — the branching is over `ℕ`, not over the symbols.

This is a theorem, not a design preference. Keep it as a permanent block: any future proposal to
encode `Sentenceω` directly is refuted by it.

**Consequence.** HF encodes the finitary fragment:

```
ℕ (sentence codes) --decode--> finitaryFragment L ⊆ L.Sentenceω
Σ-definition codes            --> c.e. sets of *sentence codes*, never of sentences
```

## 2. One ambient `Element`, not separate sorts

Separate sorts and an ambient carrier are **inter-translatable** (subtypes one way, `Sum` the other),
so this was never a question of expressiveness. Two things decide it:

**KP closure discriminates.** Pairing and union are operations on *elements*; they do not respect the
kind subdomains — the pair of a sentence code and a definition code is an element and typically has
no kind at all. One carrier states them directly; separate sorts must route every closure law
through `Sum`.

**The frozen design is already ambient-shaped.** `AdmissiblePresentation.Code` serves *both*
`DecodesFamily` and `DecodesTheory`, and `CodedFamily.lean` says so outright: "the same codes (the
elements of `A`) but a different thing named." Separate sorts would be the first departure from that.

**Kind naming.** `DecodesTheory` identifies an **`IsTheoryCode`** — a set of sentences named
*extensionally* — not an `IsDefinitionCode`, which names one *intensionally*. Four kinds: family,
theory, sentence, Σ-definition. Kinds may **overlap**; in HF every code is a number.

## 3. Σ-definition codes carry sentence codes

Sentence decoding is **functional but not injective** — a sentence may have many codes. Because a
Σ-definition code carries a set of *sentence codes* and the theory it defines is the decoded
**image**, functionality of `DefinesSigmaTheory` holds **by construction**. The extensionality law
that multiple codes per sentence would otherwise force is free. This is the payoff of coding
sentence codes rather than sentences, and it is why the production field set needs no
`definesSigmaTheory_unique` beyond `h.trans h'.symm`.

**Totality must be omitted.** A presentation is not obliged to name every theory, and honest HF must
not. Functionality alone still injects the *definable* theories into the codes, which is all the
counting arguments need.

**`DefinitionCode := Set L.Sentenceω` is the negative control** — a faithful implementation of the
old `Sigma1 := True` enlargement, nothing more. Not an endpoint.

## 4. Containment is derived, not removed

`subset_of_sigma1` shows codes cannot reach outside their decoded range. But that yields `T ⊆ P`
**only after an adequacy equation** identifies the range with `P`. Therefore:

- the generic `CompactFor A P T` **keeps** its `T ⊆ P` hypothesis;
- a presentation-relative wrapper derives containment from adequacy internally;
- the wrapper must use the presentation's **own** `Sigma1`, not a free `Sig` parameter — an
  arbitrary `Sig` recreates the generic compactness wrapper this contract deliberately avoids.

## 5. "c.e." means `Nat.Partrec`

An existential over an arbitrary `W : ℕ → Set ℕ` has **no computability content**. The honest
definition is `CE S := ∃ f : ℕ →. ℕ, Nat.Partrec f ∧ ∀ n, n ∈ S ↔ (f n).Dom`, and
`Nat.Partrec.Code.exists_code` shows c.e. sets are exactly the domains of `Nat.Partrec.Code`s — so
`DefinitionCode := Nat.Partrec.Code` is *complete* for c.e.-ness rather than a modelling convenience.

`[Encodable L.Sentence]` supplies syntax coding only. It does not make arbitrary subsets c.e.

## 6. The three placeholders — all closed

Named explicitly because each *looked* like a constraint and was not one. All three are now
discharged in `InfinitaryLogic/Admissible/{Ackermann,Ambient,AmbientHF,Numbering}.lean`.

**(a) The numbering — RESOLVED by a second layer, not by strengthening the first.** `FinitaryCoding`
stores `enc` and injectivity. Injectivity gives numbering-independence of the *decoded range* — hence
of adequacy and containment, which is `hfAmbient_range_indep` — but **not** of `Sigma1`: two
injective numberings can disagree about which theories are c.e.

The fix is not a stronger single numbering. It is a **relation** between numberings, so
`FinitaryCoding` is left alone and the new layer is added *beside* it, in
`InfinitaryLogic/Admissible/Numbering.lean`:

```
FinitaryCoding              adequacy, AFinite, and Sigma1 itself   -- any language
FinitaryNumbering           a *bijective* numbering; no effectiveness on its own
ComputablyEquivalent C C'   Sigma1 invariance                      -- the actual content
```

**Read the middle line carefully — an earlier draft of this section overclaimed here.**
`Sigma1` is *already* definable from the weak layer: `hfAmbient` takes a `FinitaryCoding` and
supplies `enumerates`, so every coding has its own coding-relative `Sigma1`. The numbering is needed
for **invariance**, not for the definition. And `FinitaryNumbering` is structurally a bijective
numbering and nothing more — `ofDenumerable` builds one from a bare `Denumerable` instance with no
computability evidence at all. It was renamed from `EffectiveCoding` precisely so the name stops
claiming effectiveness it does not have; effectiveness enters only at
`ComputablyEquivalent.forward_computable`. **Independence holds only when a witness is supplied.**

`FinitaryNumbering.Sigma1 T := (hfAmbient C.toFinitaryCoding).Sigma1 T` is the production-facing
predicate — definitionally the ambient one, named separately so consumers state hypotheses against a
numbering, which is what makes invariance applicable to them. Use it in migration stage 5.3.

The six gates, by the semantic names they now carry (the numbering survives only here):

| # | Statement | Name |
|---|---|---|
| 1 | translation preserves the decoded sentence | `ComputablyEquivalent.decodeSentence_forward` |
| 2 | no invalid inputs to bookkeep | `FinitaryNumbering.invalid_codes_eq_empty` |
| 3 | …the reverse translation likewise | `ComputablyEquivalent.decodeSentence_backward` |
| 4 | c.e. code sets transport | `ComputablyEquivalent.ce_forward_image` |
| 5 | `Sigma1` is numbering-independent | `AreComputablyEquivalent.sigma1_iff` |
| 6 | the weak layer suffices downstream | `hfAmbient_rejects_numbering` + two examples |

Gate 6 needs the guard, not the examples. Positive theorems show weak data *suffices*; they cannot
detect a future widening of `hfAmbient`. `hfAmbient_rejects_numbering` carries a `fail_if_success`
on `hfAmbient C` and then proves adequacy through `.toFinitaryCoding`, so it asserts both halves.
Verified live: `fail_if_success` on the *working* forgetful route does itself fail, so the guard
discriminates rather than passing vacuously.

*The bijectivity simplification.* `enc` is required to be onto, so every natural is a valid code and
invalid-code bookkeeping disappears: gate 2 becomes *provably vacuous* rather than dropped, and the
translations become mutually inverse computable permutations, so image along one is preimage along
the other and gate 4 needs no dovetailing. The cost is explicit in `FinitaryNumbering.equiv`: the
layer exists exactly when `L.Sentence` is denumerable — the intended setting — and `ofDenumerable`
witnesses that it is inhabited, so nothing is conditionally vacuous. Languages outside it keep the
weak layer and correctly get no numbering at all.

*Prop vs Type.* `ComputablyEquivalent` stores `forward`/`backward`, so it cannot be `Prop`-valued.
The public relation is `AreComputablyEquivalent C C' := Nonempty (ComputablyEquivalent C C')`, an
equivalence relation (`refl`/`symm`/`trans`, with `ComputablyEquivalent.trans` composing the
translations underneath).

**(b) The `A`-finite layer — RESOLVED, and it corrects an API.** `IsTheoryCode` and `decodeTheory`
are now **derived**, not fields: given ambient membership, a theory code is an element all of whose
members are sentence codes, and the theory it names is their decoded image. Deriving them is what
keeps `Mem` honest — a stored `decodeTheory` would hide a vacuous membership relation.

The correction: **`hf_aFinite_iff`'s global `AFinite T ↔ T.Finite` does not survive.** Theory codes
are built from *finitary* sentence codes, so a finite theory containing an infinitary sentence is
simply not an element of HF. The honest endpoint is

```
AFinite T ↔ T.Finite ∧ T ⊆ finitaryFragment L                    -- hfAmbient_aFinite_iff
T ⊆ finitaryFragment L → (AFinite T ↔ T.Finite)                  -- ..._of_finitary
```

The old global form is a harmless enlargement on `hfPresentation`'s current compactness domain, but
preserving it here would mean encoding infinitary sentences into HF, which §1 rules out.
`not_hfAmbient_aFinite_iff_finite` **exhibits** a finite non-`A`-finite theory — a singleton `iInf`
— so the equation cannot be quietly restored "for compatibility" during the production migration.

**(c) The KP fields were vacuous — RESOLVED for pairing and union.** `pair_total : ∀ a b, ∃ c,
Pair a b c` with no specification law is satisfied by `Pair := fun _ _ _ => True` on any inhabited
carrier. Totality is not pairing. `AmbientPresentation` now carries ambient membership, and `WithKP`
pins each operation by a law against it:

```
mem_pair  : Mem x (pair a b) ↔ x = a ∨ x = b
mem_union : Mem x (union a)  ↔ ∃ y, Mem y a ∧ Mem x y
```

`Nat.AckMem` (`∈ₐ`, bit `a` of `b`) implements it, `hfAmbientKP` is then a structure literal, and
`Nat.finite_ackMem` / `Nat.exists_ack_of_finite` — codes name *exactly* the finite sets — are what
make (b) provable.

The rest of KP stays **deferred, not forgotten**: the #19A source audit must first identify which
closure and absoluteness laws later proofs actually consume.

## 7. Two questions that must not be merged

- **Effective countability** needs explicit coding of language symbols and finitary syntax.
  **`Language.{0, 0}` does not imply countability** — universe zero contains uncountable types.
- **The model universe** built by compactness is a separate **#19B** decision and cannot be inferred
  from any coding result.

Note `HF.lean` declares `variable {L : Language.{0, 0}}`, so the HF compactness oracle is pinned to
universe-zero languages while `hfPresentation` around it is polymorphic. The cause is
`Theoryω.IsSatisfiable`, whose model is `M : Type`. This is a fact to explain, not evidence for
either side of the model-universe question.

## 8. The tranche

1. ~~**Freeze the layered production interface**~~ — **DONE** (`Ambient.lean`): one ambient `Element`
   with family, theory, sentence and Σ-definition subdomains.

   *An earlier version of this line claimed `CodedFamily` "still depends only on the family layer".
   That was false when written* — `CodedFamily` was parameterized by the whole
   `AdmissiblePresentation`, `Sigma1` included, and the ambient `IsFamilyCode` had no `Index` /
   `DecodesFamily` behind it, so no coded family could be built from an ambient presentation at all.
   It became true only with migration stage 5.1 below.
2. ~~**Honest HF theory coding**~~ — **DONE** (`AmbientHF.lean`): sentence codes from the stored
   finitary coding, theory codes exactly the finite sets of sentence codes, `decodeTheory` as their
   decoded image. The characterization is `AFinite T ↔ T.Finite ∧ T ⊆ finitaryFragment L`, **not**
   the global `↔ Set.Finite` originally written here — see §6(b).
3. ~~**Honest effective coding**~~ — **DONE** (`Numbering.lean`): a *second* layer beside
   `FinitaryCoding`, not a strengthening of it; six gates, ending in
   `AreComputablyEquivalent.sigma1_iff`; §6(a).
4. ~~**Meaningful KP**~~ — **DONE** (`Ackermann.lean`, `WithKP`, `hfAmbientKP`), for pairing and
   union only; §6(c).

**Steps 1–4 are complete. Everything below is unstarted.**

5. **Production migration**, staged — each stage its own commit, each independently green:
   1. ~~move `CodedFamily` onto the ambient **family** layer~~ — **DONE** (`Family.lean`).
      `FamilyPresentation` is the minimal view: ambient `Element`, `IsFamilyCode`, code-dependent
      `Index`, stored `indexEncodable`, `DecodesFamily`, and functionality — which is
      *unconditional* here because the old `CodesInfFamily` hypothesis is absorbed into the code
      subtype. `CodedFamily`, `codedIInf`, `codedISup` and `AdmissibleFragment` take that view;
      `AdmissiblePresentation.toFamilyPresentation` is the explicit projection, and
      `AmbientPresentation` now **extends** the view instead of duplicating `IsFamilyCode`.
      Separation is by import — `Family.lean` is imported *by* the theory/Σ files — and pinned by
      `scripts/check_family_cone.lean`.

      *On how that guard is falsification-tested.* It was originally checked by adding
      `hfAdmissibleFragment` as a root and confirming it reported `AdmissiblePresentation`. That
      witness is **gone**: stage 5.4's preparation moved `hfAdmissibleFragment` onto `hfFamily`, so
      it is now a permanent *passing* root. The current controls are:

      - **positive witness** — `hf_compactFor` as a root makes the guard report
        `AdmissiblePresentation.AFinite` and `.CompactFor`;
      - **proof-only negative control** — `hfAmbient_compact` names no legacy declaration in its
        type, yet reaches `AdmissiblePresentation` through its proof body.

      The control runs the cone **twice**, which is what makes it durable: `depsWith false`
      (types and `def` bodies, no theorem bodies) must *not* reach `AdmissiblePresentation`, and
      `depsWith true` must. Inspecting direct constants cannot establish "reachable only through
      bodies" — a type-side path elsewhere in the cone would go unnoticed. Two further assertions
      keep it honest: `AdmissiblePresentation` must be absent from the probe's own value, so the
      full traversal is exercising transitivity rather than a one-hop lookup, and
      `hf_compact_of_aFinite` must be present there but absent from the type.

      Falsification-tested in three modes, each producing a distinct message: theorem bodies not
      followed while `declValue?` still returns a value — the bug an earlier, weaker version of
      this control could not see, because it failed at "no value" for a different reason; a
      `leaked` name reachable in one hop; and a `leaked` name reachable without any theorem body.
   2. ~~move `AFinite` onto the derived `decodeTheory`~~ — **DONE** (`Theory.lean`).
      `TheoryPresentation` is the middle layer: `FamilyPresentation` + `Mem` + `IsSentenceCode` +
      `decodeSentence`, with `IsTheoryCode` / `decodeTheory` / `AFinite` / `AFinitelySatisfiable` /
      adequacy **derived**. `AmbientPresentation` extends it and keeps only `IsDefinitionCode`,
      `enumerates` and `Sigma1`. The shortcut avoided: defining the production `AFinite` as
      `AmbientPresentation.AFinite` would type-check and make the whole theory API depend on the Σ
      layer that no theory-side proof uses. Pinned by `scripts/check_theory_cone.lean`.

      *The legacy route could not be projected, only isolated.* `AdmissiblePresentation` stores
      `DecodesTheory` as an arbitrary relation and has no `Mem` or `decodeSentence`, so there is
      nothing to derive a theory view from — no `toTheoryPresentation` exists, and the absence is
      the honest measure of how far the migration has got. Its predicates are now namespaced
      (`AdmissiblePresentation.AFinite`, `.ACEnumerable`, `.AFinitelySatisfiable`, `.CompactFor`)
      so every legacy use site says so; stage 5.4 retires them with `hfPresentation`.
      `hf_compact_of_aFinite` is preserved, and `hfAmbient_aFinite_iff` is unchanged.
   3. ~~replace the bare `Sigma1` field with definition-code data~~ — **DONE** (`Ambient.lean`).
      `AmbientPresentation.ACEnumerable A T := A.Sigma1 T` and

      ```
      A.CompactFor P T := T ⊆ P → A.ACEnumerable T →
                          A.toTheoryPresentation.AFinitelySatisfiable T → T.IsSatisfiable
      ```

      The `T ⊆ P` hypothesis **stays**: a presentation need not be adequate for the `P` a caller
      has in mind. `compactFor_of_adequate` is the separate assembly theorem that discharges it
      from `A.AdequateFor P` + `A.Sigma1 T` via `subset_of_adequate` — a statement the legacy route
      could not make, because a bare `Prop` on a set carries no representation data to derive
      containment from.

      HF now inhabits the honest route: `hfAmbient_compact` states both premises over `hfAmbient`
      with no legacy predicate, and `hfAmbient_compactFor` is the assembled instance. The bridge is
      `hfAmbient_aFinitelySatisfiable_iff` — the two Barwise premises are *not* equivalent in
      general (legacy `A`-finite is every finite theory, honest is the finite *finitary* ones) but
      coincide inside the fragment, since a finite subtheory of a finitary theory is finitary.

      **The legacy *theory/definability* route is obsolete — the legacy cluster is not.** An
      earlier version of this line said "the legacy cluster is obsolete", which was wrong:
      `hfPresentation` was still supplying the HF **family** view to three syntax consumers
      (`isEmpty_codedFamily_hf`, `hf_coded_closure_vacuous`, `hfAdmissibleFragment`), so deleting
      it would not have been a matter of replacing one compactness proof.

      That is now fixed ahead of stage 5.4: `hfFamily` (`Family.lean`) is the family-layer HF
      presentation — `Element := ℕ`, `IsFamilyCode := False`, the rest vacuous — the three syntax
      consumers are stated over it, and `hfAmbient_toFamilyPresentation` proves
      `(hfAmbient C).toFamilyPresentation = hfFamily L` by `rfl`. All four are now roots of
      `check_family_cone.lean`, so their independence from the legacy presentation is enforced
      rather than asserted.

      What `hfPresentation` still supplies is exactly the theory side: `hf_aFinite_iff`,
      `hf_aFinitelySatisfiable_iff`, `hf_compact_of_aFinite`, `hf_compactFor`, and the bridge
      `hfAmbient_aFinitelySatisfiable_iff`.
   4. ~~install the honest HF instance and delete the legacy cluster~~ — **DONE**, in two commits.

      *5.4a* reproved `hfAmbient_compact` through `finitaryFragment_compact` directly, via
      `hfAmbient_isFinitelySatisfiable`, retiring the `hfAmbient_aFinitelySatisfiable_iff` bridge.
      Verified by cone inspection that neither legacy name remained reachable. That change broke
      both negative controls, exactly as predicted, so the replacement triple
      (`hfAmbient_compact` / `finitaryFragment_compact` / `foTheory`) landed with it.

      *5.4b* deleted `AdmissiblePresentation`, its four namespaced predicates, `DecodesTheory`
      with `decodes_theory_unique`, the bare `Sigma1` field, `hfPresentation` and its five
      theorems — `Admissible/CodedFamily.lean` and `Admissible/Predicates.lean` went with them,
      both having become empty. The guard migration landed in the same commit, as required: the
      `[STALE GUARD]` existence check made it mandatory rather than optional.

   5. ~~reprove the generic HF compactness route without the trivial bridge~~ — **DONE** in 5.4a;
      `hfAmbient_compact` now reaches Mathlib compactness directly.
   6. **strengthen** the absence and assembly guards. Baseline guard migration already happened in
      5.4b; what remains is genuinely new coverage, not catch-up. Two kinds are required:

      **Absence.** Assert that `AdmissiblePresentation`, its four predicates, `hfPresentation`,
      `DecodesTheory` and `decodes_theory_unique` are **absent from the environment**. A deleted
      name needs an absence assertion, not a stale-forbidden entry: the `[STALE GUARD]` check
      *rejects* names that no longer exist, so a forbidden-list entry is exactly the wrong tool
      here and would fail the guard rather than protect anything.

      **Assembly.** Assert that `hfAmbient_compactFor` exposes the honest
      `AmbientPresentation.CompactFor` and reaches `hfAmbient_compact`, and that
      `compactFor_of_adequate` reaches `subset_of_adequate`. That pins both the containment
      derivation and the final compactness route, neither of which any absence check can see.

   7. **make the model-universe boundary executable — do not widen it.** Generalizing model
      universes belongs to #19B, not here. What #19A should record is where the boundary actually
      falls, as compiling probes:

      - *positive* — `hfAmbient`, adequacy and `A`-finiteness elaborate at `Language.{u, v}`;
      - *positive* — `hfAmbient_compact` elaborates at `Language.{0, 0}`;
      - *negative* — applying it to a genuinely higher-universe language fails, **while the
        representation layer still succeeds**.

      The negative control is the informative one: it states the precise result, that coding is
      universe-general while the satisfiability / first-order-compactness endpoint is
      universe-zero. Without it the restriction looks like it might be a coding limitation.

   `hf_compact_of_aFinite` is **gone**, not preserved: its content survives as `hfAmbient_compact`
   over the ambient presentation. The instruction to preserve it belonged to the staged migration,
   where it had consumers; at the end of the migration it has none.
6. **Land #19A** — before any Henkin/#19B work begins.

### Release gates for the #19A PR

**The #19A release is BREAKING — it must not be called `v2.3.0`.** Stage 5.4 deletes
`AdmissiblePresentation` together with its published predicates (`AFinite`, `ACEnumerable`,
`AFinitelySatisfiable`, `CompactFor`), `DecodesTheory` and `decodes_theory_unique`. Those are
shipped API as of v2.0.0, so removal is a major bump — the same reasoning that made v2.0.0 major
rather than v1.9.0. Decide the number when the PR is cut, but not from the 2.x line.

**Merge current `master` first, then rerun the full gate.** The branch is based at v2.1.0 while
`master` has moved to v2.2.0 (`db7c49b`). Deferring the merge is safe *today* — v2.2.0's changes
are confined to `ModelTheory/BF*`, `ModelTheory/MorleyCounting.lean` and `Descriptive.lean`, which
this branch does not touch, so the file-overlap is empty — but that is a fact about today, not a
standing guarantee. Re-check before the PR rather than trusting this line.

**Rewrite `docs/admissible-interface-contract.md` to present state.** It still presents deleted
declarations as the implemented current API — `AdmissiblePresentation`, `hfPresentation`,
`DecodesTheory`, `decodes_theory_unique`, the old predicates and the old oracle table — under a
"Status: implemented" heading, citing a file that no longer exists. That is **factually stale, not
historical narration**, and the distinction matters: this checkpoint is where migration history
belongs, the contract is a statement about what the API *is*. It now carries a staleness banner so
it cannot mislead in the interim, but the banner is not the fix.

**Strip the stage-by-stage migration narration from production docstrings.** `Family.lean`,
`CodedFamily.lean`, `Theory.lean`, `Ambient.lean`, `AmbientHF.lean`, `Numbering.lean` and
`Predicates.lean` currently narrate *which stage* moved what, and why an earlier arrangement was
wrong. That belongs here, in the checkpoint — not in the settled API, where it will read as
archaeology to anyone who never saw the migration.

Deliberately deferred rather than done incrementally: later stages add more of it, so a single pass
at the end is one edit instead of several. Do not let the PR go out without it.

### The remaining order

1. 5.6 — absence and assembly guards.
2. 5.7 — executable universe boundary.
3. Rewrite the public contract and strip production archaeology.
4. Merge current `master` and rerun every gate.
5. Open the breaking #19A PR; choose the next major version only **after** merge.
