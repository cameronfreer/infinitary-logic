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
| `FinitaryCoding` is an *acceptable* numbering | **placeholder** — only injective |
| The `A`-finite / theory-code layer | **placeholder** — `IsTheoryCode` is trivial, no `decodeTheory` |
| KP closure | **placeholder** — the fields are vacuous, see §6 |

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

## 6. The three placeholders

Named explicitly because each currently *looks* like a constraint and is not one.

**(a) `FinitaryCoding` is not an acceptable numbering.** It stores `enc` and injectivity. Injectivity
gives numbering-independence of the *decoded range* — hence of adequacy and containment — but **not**
of `Sigma1` itself. Two injective numberings can disagree about which theories are c.e. Either store
a canonical numbering with the required `Nat.Partrec` properties, or state the whole Σ-layer
explicitly relative to a chosen effective presentation.

**(b) The `A`-finite layer is not reconstructed.** `IsTheoryCode n := ∃ k : ℕ, n = k` is
definitionally `True`, and `AmbientPresentation` has no `decodeTheory`. So the ambient interface does
not yet carry `AFinite` at all.

**(c) The KP fields are vacuous.** `pair_total : ∀ a b, ∃ c, Pair a b c` with no specification law is
satisfied by `Pair := fun _ _ _ => True` on any inhabited carrier. Totality is not pairing. The fix
is an ambient membership relation plus laws:

```
Pair a b c  ↔ ∀ x, x ∈ₐ c ↔ x = a ∨ x = b
Union a c   ↔ ∀ x, x ∈ₐ c ↔ ∃ y, y ∈ₐ a ∧ x ∈ₐ y
```

Do **not** attempt all of KP now: the #19A source audit must first identify which closure and
absoluteness laws later proofs actually consume.

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

1. **Freeze the layered production interface** — one ambient `Element` with family, theory, sentence
   and Σ-definition subdomains. `CodedFamily` depends only on the family layer; effective Σ-data must
   not infect the syntax interface.
2. **Honest HF theory coding** over Ackermann-coded finite sets on `ℕ`: sentence codes from the
   stored finitary coding, theory codes exactly the finite sets of sentence codes, `decodeTheory` as
   their decoded image, and `AFinite ↔ Set.Finite`.
3. **Honest effective coding** — §6(a).
4. **Meaningful KP** — §6(c), with Ackermann membership for the HF instance.
5. **Production migration** — replace the bare `Sigma1` field with definition-code data; make
   `ACEnumerable` existential over those codes; delete `hfPresentation_sigma1_eq_top`; preserve
   `hf_compact_of_aFinite`; prove the generic HF compactness route without the current trivial
   bridge; recheck the four consumers.
6. **The model-universe gate**, separately.
7. **Guards, then land #19A** — before any Henkin/#19B work begins.
