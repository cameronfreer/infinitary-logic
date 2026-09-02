# The admissible-presentation interface (issues #18, #19A)

What the admissible layer **is**. This document describes the implemented API and the boundaries it
enforces; it is not a plan, and it records no history. Migration history, superseded designs, and
the reasoning that produced these choices live in `docs/admissible-19a-checkpoint.md`.

---

## 1. The presentation tower and the import boundary

Three structures, each in its own file, each extending and imported *by* the next:

```
FamilyPresentation      Element, IsFamilyCode, Index, indexEncodable, DecodesFamily
                                                                    -- Admissible/Family.lean
        ↑
TheoryPresentation      + Mem, IsSentenceCode, decodeSentence
                        + derived IsTheoryCode / decodeTheory / AFinite
                                                                    -- Admissible/Theory.lean
        ↑
AmbientPresentation     + IsDefinitionCode, enumerates
                        + derived Sigma1                            -- Admissible/Ambient.lean
```

**One ambient `Element` carries all codes.** The four kinds — family, theory, sentence,
Σ-definition — are subdomains of it and may overlap; in HF every code is a natural number, so they
overlap totally. One carrier rather than separate sorts because KP closure discriminates: pairing
and union are operations on *elements* and do not respect the kind subdomains, so separate sorts
would route every closure law through `Sum`.

**The layering is enforced by types and imports, not by convention.** The syntax layer cannot
mention theory decoding; the theory layer cannot mention `Sigma1`, definition codes, KP or
numberings — they are defined in files that import it. Two guards pin this permanently:

| Guard | Pins |
|---|---|
| `scripts/check_family_cone.lean` | the syntax API depends only on `FamilyPresentation` |
| `scripts/check_theory_cone.lean` | the theory API depends only on `TheoryPresentation` |

Both traverse theorem bodies, and both carry a `[STALE GUARD]` check requiring every forbidden name
to still exist — a forbidden entry naming something deleted protects nothing.

---

## 2. Certified infinitary families

`CodedFamily P n` bundles a code, its decoding into `L.BoundedFormulaω Empty n`, and the
certificate that the code names a family. `codedIInf` and `codedISup` build the named conjunction
and disjunction.

Three details are load-bearing:

1. `decode` lands in the structure's own arity, so no independent arity field can drift.
2. The enumeration is supplied by the presentation (`indexEncodable`), keyed on the code, **not**
   found by instance search — so the syntax a coded family builds depends on the code.
   `codedIInf_uses_presentation_encoding` states this.
3. `IsFamilyCode` is a **certificate**, carried in the code subtype. Without it any code with any
   decoding would build a coded family, and "HF has no primitive coded families" would be
   unstatable.

`decodes_unique` makes decoding code-determined, which is what `decode_eq_of_code_eq`,
`codedIInf_eq_of_code_eq` and `codedISup_eq_of_code_eq` rest on.

`AdmissibleFragment` (`Admissible/Fragment/Honest.lean`) is an ordinary `Fragment` closed upward
under exactly the conjunctions and disjunctions named by *certified* coded families — and nothing
else. It carries **no** `height` field and **no** compactness field; compactness is a theorem with
hypotheses, proved externally, which is what makes "a theorem named Barwise compactness merely
projects a field" structurally impossible rather than merely observed.

---

## 3. Derived theory codes and `AFinite`

`IsTheoryCode` and `decodeTheory` are **not** fields. Given ambient membership, a theory code is an
element all of whose members are sentence codes, and the theory it names is the decoded image of
those members.

Deriving them is what keeps `Mem` honest: a vacuous membership relation would collapse the theory
layer, and a stored `decodeTheory` field would hide that.

```lean
AFinite T                 := ∃ a : TheoryCode, decodeTheory a = T
AFinitelySatisfiable T    -- the Barwise premise, over A-finite subtheories
AdequateFor F             := sentenceRange = F
```

**Functionality is free.** A theory code names an *image*, not a relation, so `AFinite.unique` is
`h ▸ h'` — no extensionality law, even though sentence decoding is non-injective.

**Totality is deliberately omitted.** A presentation is not obliged to name every theory, and an
honest HF must not: `AFinite` is existential over codes, never a bijection with theories.

`AFinite.subset_of_adequate` derives fragment containment from adequacy rather than assuming it.

---

## 4. Definition codes, `Sigma1`, adequacy and containment

A Σ-definition code carries a set of *sentence codes*; `theoryOf` decodes their image, and

```lean
Sigma1 T      := ∃ d : DefinitionCode, theoryOf d = T
ACEnumerable  := Sigma1                    -- the Barwise Σ-definability premise
```

`Sigma1` is derived from `enumerates`, not stored, and `Sigma1.unique` is again `h ▸ h'` for the
same image-not-relation reason.

**`ACEnumerable` is not an arbitrary `Prop` on a set.** Unfolding it produces a definition *code*,
and that is exactly what makes containment derivable:

```lean
subset_of_adequate : A.AdequateFor F → A.Sigma1 T → T ⊆ F
```

A bare predicate on sets carries nothing from which containment could be obtained.

`AmbientPresentation.WithKP` adds pairing and union **with specification laws**, not merely
totality. Totality alone is vacuous: `pair_total : ∀ a b, ∃ c, Pair a b c` is satisfied by
`Pair := fun _ _ _ => True` on any inhabited carrier. The full KP schema is deliberately not
attempted; which closure and absoluteness laws are needed is settled by the proofs that consume
them, and no such proof exists yet.

---

## 5. The HF instance: Ackermann coding and corrected finiteness

`Element := ℕ` under Ackermann membership (`Admissible/Ackermann.lean`): `a ∈ₐ b` means bit `a` of
`b` is set, so every natural is a finite set of naturals and the coding is total both ways.
`Nat.ack_ext` gives extensionality; `Nat.mem_ackPair` and `Nat.mem_ackUnion` are the specification
laws; `Nat.finite_ackMem` and `Nat.exists_ack_of_finite` say codes name exactly the finite sets.

`hfAmbient C` is the ambient presentation over a stored `FinitaryCoding C` — an injective numbering
of the *finitary* sentences. `hfAmbientKP` discharges pairing and union by Ackermann arithmetic.

**`A`-finiteness is not plain finiteness.** Theory codes are built from finitary sentence codes, so
a finite theory containing an infinitary sentence is not an element of HF:

```lean
hfAmbient_aFinite_iff : AFinite T ↔ T.Finite ∧ T ⊆ finitaryFragment L
```

Both conjuncts are necessary, and `not_hfAmbient_aFinite_iff_finite` **exhibits** a finite
non-`A`-finite theory rather than merely asserting the distinction. The global form
`AFinite T ↔ T.Finite` is false here. `hfAmbient_aFinite_iff_of_finitary` is the consumer-friendly
specialization.

`hfAmbient_adequate` gives `sentenceRange = finitaryFragment L`, and `hfAmbient_range_indep` says
the decoded range does not depend on which injective coding was stored.

---

## 6. Numberings and computable equivalence

Injectivity gives range-independence — hence adequacy and containment — but **not** `Sigma1`
independence: two injective numberings can disagree about which theories are c.e. That is a
separate layer (`Admissible/Numbering.lean`):

```
FinitaryCoding              adequacy, AFinite, and Sigma1 itself      -- any language
FinitaryNumbering           a *bijective* numbering; no effectiveness on its own
ComputablyEquivalent C C'   Sigma1 invariance across numberings       -- the actual content
```

`FinitaryNumbering` is structurally a bijective numbering and nothing more —
`FinitaryNumbering.ofDenumerable` builds one from a bare `Denumerable` instance, with no
computability evidence. Effectiveness enters only at `ComputablyEquivalent.forward_computable`, and
invariance (`sigma1_iff`) holds only against such a witness.

Bijectivity makes every natural a valid sentence code, so `invalid_codes_eq_empty` states the
invalid-input obligation is vacuous rather than dropping it, and forward/backward become mutually
inverse computable permutations — image along one is preimage along the other
(`forward_image_eq_backward_preimage`), so c.e. transport needs only closure under computable
preimage, with no dovetailing. `equiv` states the cost: a `FinitaryNumbering` exists exactly when
`L.Sentence` is denumerable.

**The layers do not mix.** `hfAmbient` takes a plain `FinitaryCoding`, so numbering data cannot
infect the fragment or theory layers. `hfAmbient_rejects_numbering` enforces that refusal with
`fail_if_success` rather than leaving it to the positive examples.

---

## 7. Compactness assembly and the universe boundary

HF inhabits the compactness interface on the honest route end to end:

```lean
CompactFor P T          := T ⊆ P → ACEnumerable T → AFinitelySatisfiable T → T.IsSatisfiable
hfAmbient_compact       -- straight to finitaryFragment_compact, i.e. Mathlib compactness
hfAmbient_compactFor    -- HF inhabits CompactFor
compactFor_of_adequate  -- the caller never supplies containment
```

`T ⊆ P` remains a genuine hypothesis on `CompactFor`: `subset_of_adequate` yields it only once an
adequacy equation identifies the decoded range with `P`, and a presentation need not be adequate for
the `P` a caller has in mind. `compactFor_of_adequate` is the wrapper that discharges it, and
`scripts/check_admissible_migration.lean` asserts both that HF exposes the real interface and that
the containment derivation is genuinely reached through the proofs.

**The universe boundary.** Representation and the low-level finitary compactness argument are
universe-general; the ambient presentation endpoint has not yet adopted the indexed result:

| | Level |
|---|---|
| `hfAmbient`, `hfAmbient_adequate`, `hfAmbient_aFinite_iff` | any `Language.{u, v}` |
| `finitaryFragment_compactIn` | any `Language.{u, v}`; output carrier in `Type (max u v)` |
| `hfAmbient_compact` | `Language.{0, 0}` |

`Theoryω.IsSatisfiableIn.{u, v, w}` makes the carrier universe explicit while the published
`Theoryω.IsSatisfiable` remains its universe-zero specialization.  The remaining restriction is in
the ambient `CompactFor` interface, **not** in Mathlib compactness or HF coding; it must not be read
back onto a syntactic definition.
`scripts/check_admissible_universes.lean` states both halves as compiling probes at explicit levels,
with a negative control exhibiting the higher-universe representation route while rejecting
compactness at the same language.

---

## 8. The proof-system boundary, and deferred scope

`Derivable`, `AConsistent` and `Derivable.sound` are parameterized by a raw `P : Set L.Sentenceω` —
no fragment structure at all.

This is not a weakening. `Derivable`'s infinitary constructors take membership as a *hypothesis*:

```lean
| iInf_intro : (∀ k, Derivable A T (φs k)) → .iInf φs ∈ A.formulas → …
```

so the upward closure over arbitrary external ℕ-indexed families — which an honest HF fragment
provably cannot satisfy — is never consumed by the proof system. Soundness accesses no field of `A`
whatsoever. The two lemmas that need negation membership (`AConsistent.no_contradiction`,
`Derivable.inconsistent_of_both_extensions`) take `φ.not ∈ P` explicitly.

`scripts/check_proof_system_boundary.lean` enforces it: the `Derivable`/soundness cone cannot reach
`FiniteCompactFragment`, `AdmissibleFragmentCore` or `BarwiseFragment`.

**Deliberately out of scope, and why:**

| Deferred | Reason |
|---|---|
| `height` on presentations or fragments | whether it belongs to the presentation or is derived is unsettled; a field would permit a fragment whose height disagreed with its presentation's |
| the full KP schema | the consuming proofs do not exist yet, so the required laws are not yet determined |
| `Admissible/Barwise/ConsistencyBridge.lean` | still built on legacy closure/completeness machinery; quarantined for #19B |
| model-universe generalization | #19B; §7 records where the boundary falls rather than moving it |
| `AdmissibleFragmentCore.hf := Set.univ` | a quarantined placeholder — nothing may be proved from it |

---

## The governing design rule

**Carry the coding data; do not replace it with the property it induces.** A presentation names
theories and definitions by *codes*, and the predicates are existentials over those codes. Every
derived result in §3, §4 and §7 — functionality for free, containment from adequacy, the assembled
compactness route — exists because the code survived into the statement. A bare `Prop` on a set
would type-check in each case and prove none of them.
