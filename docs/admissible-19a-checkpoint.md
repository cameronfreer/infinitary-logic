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
| `FinitaryCoding` is an *acceptable* numbering | **placeholder** — only injective, §6(a) |
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

## 6. The three placeholders — one open, two closed

Named explicitly because each *looked* like a constraint and was not one. Two are now discharged in
`InfinitaryLogic/Admissible/{Ackermann,Ambient,AmbientHF}.lean`; (a) remains open and is next.

**(a) `FinitaryCoding` is not an acceptable numbering — STILL OPEN.** It stores `enc` and
injectivity. Injectivity gives numbering-independence of the *decoded range* — hence of adequacy and
containment, which is `hfAmbient_range_indep` — but **not** of `Sigma1` itself. Two injective
numberings can disagree about which theories are c.e. Either store a canonical numbering with the
required `Nat.Partrec` properties, or state the whole Σ-layer explicitly relative to a chosen
effective presentation.

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
   with family, theory, sentence and Σ-definition subdomains. `CodedFamily` still depends only on the
   family layer; effective Σ-data does not infect the syntax interface.
2. ~~**Honest HF theory coding**~~ — **DONE** (`AmbientHF.lean`): sentence codes from the stored
   finitary coding, theory codes exactly the finite sets of sentence codes, `decodeTheory` as their
   decoded image. The characterization is `AFinite T ↔ T.Finite ∧ T ⊆ finitaryFragment L`, **not**
   the global `↔ Set.Finite` originally written here — see §6(b).
3. **Honest effective coding** — §6(a). **This is the next step.**
4. ~~**Meaningful KP**~~ — **DONE** (`Ackermann.lean`, `WithKP`, `hfAmbientKP`), for pairing and
   union only; §6(c).
5. **Production migration** — replace the bare `Sigma1` field with definition-code data; make
   `ACEnumerable` existential over those codes; delete `hfPresentation_sigma1_eq_top`; preserve
   `hf_compact_of_aFinite`; prove the generic HF compactness route without the current trivial
   bridge; recheck the four consumers.
6. **The model-universe gate**, separately.
7. **Guards, then land #19A** — before any Henkin/#19B work begins.
