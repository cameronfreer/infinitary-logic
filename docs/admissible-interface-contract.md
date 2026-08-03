# The admissible-fragment interface contract (issue #18)

**Status: implemented.** The contract below was written and tested on paper against the HF oracle
first; it is now realized in `Admissible/CodedFamily.lean`, `Admissible/Fragment/Honest.lean` and
`Admissible/HF.lean`, all on the `InfinitaryLogic.Admissible` bundle surface. Two departures from the
text below were forced by implementation and are recorded here rather than silently absorbed:

* **`height` was dropped from `AdmissibleFragment`** (§3 proposes it). Whether height belongs to the
  presentation or is derived from it is unsettled, and a field on the fragment would permit a
  fragment whose height disagreed with its presentation's. It returns with #19A.
* **`CodedFamily` is indexed by the presentation alone**, `CodedFamily A n` — the language is
  recovered from `A`, so the separate `L` parameter in §2's sketch does not appear.

The oracle conditions in §5 are discharged in Lean: condition 1 by `sentence_slice_hfFragment`,
condition 2 by `isEmpty_codedFamily_hf`, condition 3 by `finitaryFragment_compact`, and condition 4
by `scripts/check_hf_compactness.lean`, which is enforced in CI.

The invariant this document exists to protect:

> **HF validates the interface; the interface does not redefine HF to fit itself.**

Every field below was checked against the HF specialization *before* being proposed. Where a natural
field fails that test, the failure is recorded rather than the field weakened silently.

---

## 0. What the spike established

`InfinitaryLogic/WIP/HFSpike.lean` (commit `25f6957`) proves, independent of every legacy structure:

```lean
def finitaryFragment (L : Language.{0,0}) : Set L.Sentenceω := Set.range Sentence.toLω

theorem finitaryFragment_compact {T : Set L.Sentenceω} (hT : T ⊆ finitaryFragment L)
    (hfin : ∀ F ⊆ T, F.Finite → ∃ M …, Theoryω.Model F M) :
    ∃ M …, Theoryω.Model T M
```

The proof consumes `Theory.isSatisfiable_iff_isFinitelySatisfiable` (Mathlib) and mentions neither
`AdmissibleFragmentCore` nor `FiniteCompactFragment`.

**The oracle.** Any proposed interface must satisfy, for its HF instance:

1. underlying formulas are exactly the `toLω`-image;
2. coded families reduce to **finite** families;
3. its compactness theorem is exactly `finitaryFragment_compact`;
4. **no adapter widens it back to all of Lω₁ω.**

---

## 1. The existing `Fragment` is the right base — and this is not obvious

`Lomega1omega/Fragment.lean` defines

```lean
structure Fragment (L) where
  toSet : Set (Σ n, L.BoundedFormulaω Empty n)
  imp_left_mem / imp_right_mem / all_mem / iInf_mem / iSup_mem : …
```

Two properties matter, and together they are why this base works where
`AdmissibleFragmentCore` does not:

- **It is all-arity.** `Σ n, BoundedFormulaω Empty n`, not just sentences. This is #18's gate 2
  already satisfied by the base.
- **Every closure field is *downward*** — "if a member is an `iInf`, its components are members" —
  never *upward*. Nothing obliges a `Fragment` to *contain* the conjunction of a family it contains.

**HF check.** The HF instance is

```
hfSet L := Set.range (fun p : Σ n, L.BoundedFormula Empty n => ⟨p.1, p.2.toLω⟩)
```

(the spike's `finitaryFragment` is the arity-0 slice). `iInf_mem` and `iSup_mem` hold **vacuously**:
`toLω` never emits an `iInf`/`iSup` constructor, so no member is one. `imp_left_mem`,
`imp_right_mem`, `all_mem` hold because `toLω` is a structural embedding — if `φ.imp ψ` is in the
image then its preimage is an implication, whose components are themselves in the image.

**This is exactly the field that killed `AdmissibleFragmentCore`.** Its `closed_iInf`/`closed_iSup`
are *upward* and quantify over **every external ℕ-family**:

```lean
closed_iInf : ∀ φs : ℕ → L.Sentenceω, (∀ k, φs k ∈ formulas) → BoundedFormulaω.iInf φs ∈ formulas
```

HF cannot satisfy this: take any `φs` constantly a member; the conjunction is a genuine `iInf` node,
which is not in the `toLω` image. The field is unsatisfiable for HF, not merely inconvenient.

---

## 2. Object 1 — `CodedFamily`

**Contract.** A coded family is a **code together with its decoding**, not a predicate on a function.

```
structure CodedFamily (A : AdmissiblePresentation) (L) (n : ℕ) where
  code    : A.Code
  decode  : A.Index code → L.BoundedFormulaω Empty n   -- lands in n; NO separate arity field
  enc     : Encodable (A.Index code)                    -- needed to BUILD an iInf/iSup
  isInf   : A.CodesInfFamily code                       -- the certificate; see below
```

Three requirements, each with a reason:

- **Data-carrying, not Prop.** `CodedFamily` must supply the family, so that "the fragment is closed
  under coded families" is a statement about objects the admissible set actually contains. A
  `Prop`-valued predicate on an arbitrary external `ℕ → Formula` cannot express that: the function
  is chosen in the metatheory, not in `A`.
- **The index type comes from the code**, `A.Index code`, not fixed as `ℕ`. This is what lets HF's
  coded families be finite and lets larger `A` have larger ones. Fixing `ℕ` here re-imports the exact
  defect being removed.
- **Naturality.** Decoding must commute with whatever code-level operations the proof system uses;
  the precise laws are fixed in #19A, but the *shape* — that `decode` is a function of `code` — is
  frozen now.

**HF check (oracle condition 2).** For HF, `A.Index code` ranges over **finite** types.

### Three Lean-level details, frozen

1. **No independent arity.** `decode` lands directly in `BoundedFormulaω Empty n`, the `n` of the
   structure. An extra `arity` field would permit a family whose arity disagrees with its use site.
2. **`A.Index code` needs `Encodable` (or `Countable` + choice) as explicit data.** This repo's
   `BoundedFormulaω.iInf` takes an **ℕ-indexed** family, so `codedIInf` cannot even be *defined*
   without transporting `A.Index code` to `ℕ`. This is data, not a side condition — it must travel
   in the structure.
3. **`isInf` is load-bearing and was missing.** Without it, *any* `code` with a `decode` builds a
   `CodedFamily`, so "HF's primitive coded families are empty" would be unstatable — HF has plenty
   of codes and plenty of finite decodings. The certificate `A.CodesInfFamily code` (equivalently, a
   separate relation) is what is **empty for HF**.
   **Finiteness of `A.Index code` is not a substitute**: a finite index type is exactly what would
   let someone build `iInf` over a padded sequence, which is the forbidden move below.

> **Frozen design decision.** For HF, `A.CodesInfFamily` has **no inhabitants at all**. Finite conjunctions remain available through ordinary first-order
> syntax (`⊓`, `⊔`), which stays inside the `toLω` image.
>
> **Do not encode a finite family as an infinite sequence padded with `⊤`/`⊥`.** That is
> semantically finitary but *syntactically* contains an infinitary constructor, so it leaves the
> `toLω` image and violates oracle condition 1. This is the single most likely way to accidentally
> cheat, and it is the sharpest test of the `CodedFamily` design.

---

## 3. Object 2 — `AdmissibleFragment`

**Contract.** Wraps `Fragment`; adds *upward* closure **only** for decoded coded families.

```
structure AdmissibleFragment (A) (L) extends Fragment L where
  iInf_coded_mem : ∀ (F : CodedFamily A L n), (∀ i, ⟨n, F.decode i⟩ ∈ toSet) →
      ⟨n, codedIInf F⟩ ∈ toSet
  iSup_coded_mem : …
  height : Ordinal          -- o(A); NO lower bound imposed
```

- **No compactness data.** Not a field, not a bundled instance. Compactness is a *theorem about* a
  fragment, proved from hypotheses, and belongs in object 3. This is the direct fix for the defect
  the claims-hygiene pass documented (`barwise_compactness` currently projects `A.compact`).
- **No `height_gt_omega`.** HF's height *is* ω. Any lower bound excludes the base case.
- `codedIInf F` is the conjunction the *code* names — its index type is `A.Index F.code`, so for HF
  it is a finite conjunction and reduces to first-order syntax.

**HF check.** With HF's coded families empty at the primitive nodes, `iInf_coded_mem` and
`iSup_coded_mem` are **vacuous** — the same way the base's downward fields are. HF instantiates
`AdmissibleFragment` honestly, with no adapter and no widening (oracle condition 4).

---

## 4. Object 3 — theory predicates and evidence, external

**Contract.** These are *never* fields of the syntax record.

```
def AFinite      (A) (T : Set …) : Prop   -- T is coded by an element of A that A believes finite
def ACEnumerable (A) (T : Set …) : Prop   -- Σ₁-on-A
theorem compactness (A) (hT : …) (hfin : …) : …   -- a THEOREM, with hypotheses
```

Rationale: separating closure assumptions from compactness conclusions is #18's gate 4, and keeping
the evidence outside the record is what makes gate 7 ("no theorem named Barwise compactness merely
projects a compact field") structurally impossible rather than merely observed.

**HF check (oracle conditions 2 and 3).** `AFinite` for HF **is** ordinary finiteness, so the
compactness statement specializes to

```
∀ F ⊆ T, F.Finite → (satisfiable) ⟹ (satisfiable)
```

which is `finitaryFragment_compact` verbatim — hypothesis for hypothesis, no adapter. Condition 3
passes by *specialization*, not by a bridging lemma.

---

## 5. Oracle results

| # | Condition | Result |
|---|---|---|
| 1 | formulas are exactly the `toLω`-image | ✅ `hfSet` is that image; base fields hold vacuously or structurally |
| 2 | coded families reduce to finite | ✅ `A.Index code` finite; primitive-node families empty by design |
| 3 | compactness is `finitaryFragment_compact` | ✅ by specialization of the external theorem, `AFinite` = finite |
| 4 | no adapter widens to all of Lω₁ω | ✅ nothing in the three objects mentions `Set.univ`; upward closure is coded-only |

**Verdict: the mathematics passes on paper.**  Implementation proceeds in this order, so that each
step is compiler-checked against the one before:

1. `hfFragment : Fragment L`, with its sentence slice proved equal to `finitaryFragment`.
   Architecture-independent, and it makes the downward-closure argument *executable* rather than
   asserted.
2. A tiny `CodedFamily` **signature spike** resolving the three frozen details above — including an
   actual definition of `codedIInf`, which is where the `Encodable` requirement bites.
3. `AdmissibleFragment` over that tested signature.
4. The honest HF instance, verifying the coded upward-closure fields are *genuinely* vacuous.
5. Only then migrate the proof system.

---

## 6. Open items for #19A, deliberately not settled here

- The concrete shape of `AdmissiblePresentation` — abstract interface versus transitive `ZFSet`.
  The roadmap leans abstract-first *provided* it exposes genuine coding/KP closure and does not hide
  compactness as an axiom. A short Lean spike decides it.
- The exact naturality laws for `decode`.
- Whether `height` should be a field or derived from the presentation.

## 7. Migration note

`AdmissibleFragmentCore.hf := Set.univ` stays labelled a **legacy placeholder** until this interface
lands. It is not to be mutated into something its fields cannot honestly support; it is to be
*replaced*, and its consumers migrated.

---

## 8. Proof-system consumer audit — the §5 step-5 gate

**Status: frozen, verified against source. No migration code written.**

§5 ends "Only then migrate the proof system." This section is that gate: a consumer-by-consumer
record of which legacy `FiniteCompactFragment` capabilities the proof system *actually* consumes.
It is deliberately stated in terms of declaration and constructor names rather than line numbers, so
it does not rot as the files move.

### The finding that governs the migration

**The proof system never consumes the fields that make the legacy record dishonest.** `Derivable`'s
infinitary constructors take membership as a *hypothesis*:

```lean
| iInf_intro : (∀ k, Derivable A T (φs k)) → .iInf φs ∈ A.formulas → …
| iSup_intro (k : ℕ) : Derivable A T (φs k) → .iSup φs ∈ A.formulas → …
```

`closed_iInf` and `closed_iSup` — the *upward* closure over arbitrary external ℕ-indexed families
that §1 shows an honest HF fragment cannot satisfy — are never used by the proof system at all.
The migration is therefore not a weakening of the proof system: it was already compatible with an
honest carrier, and only its **parameter type** was not.

### Consumer table

| Consumer | What it actually consumes |
|---|---|
| `Derivable` constructors | `_ ∈ A.formulas` only, in `assumption`, `falsum_elim`, `imp_intro`, `iInf_intro`, `iSup_intro`, `all_intro`, `eq_refl`, `eq_subst`, `em`. No closure field, no `compact`, no `height` |
| `AConsistent` | `Derivable` only |
| `Derivable.sound` | **Nothing.** No field of `A` is accessed anywhere in its proof; `A` is a phantom parameter, present only to index `Derivable`. Corroborated by `AConsistent.of_has_model`, which already marks its fragment-containment hypothesis unused |
| Basic consistency lemmas | `closed_neg`, at exactly two sites — `AConsistent.no_contradiction` and `Derivable.inconsistent_of_both_extensions` — both wanting the same thing, `φ.not ∈ permitted` |
| `ConsistencyBridge` | Substantial legacy closure/completeness machinery. **Quarantine for #19B**; not part of this tranche |
| EM `FragmentAdapter` | `A.formulas` only inside `⊆ A.formulas` containment hypotheses, plus `barwise_compactness`. Never touches a closure field — containment and compactness are already separate arguments, so this is a signature change, not a proof restructure |

### Frozen conclusions

- `Derivable` and `AConsistent` need only `P : Set L.Sentenceω`.
- **No closure field and no distinguished-element field is required.**
- The two `closed_neg` consumers receive `φ.not ∈ P` explicitly.
- Soundness is completely independent of fragment structure.
- An optional `falsum_mem` hypothesis belongs only on a later theorem that demonstrably needs it —
  **not in the carrier API.**

### One correction, recorded because it is easy to re-derive wrongly

`Derivable` does **not** implicitly require `falsum_mem`. In

```lean
| falsum_elim : Derivable A T .falsum → φ ∈ A.formulas → Derivable A T φ
```

the membership premise concerns the arbitrary *conclusion* `φ`, not `.falsum`. Likewise
`AConsistent P T := ¬ Derivable P T .falsum` is definable without `.falsum ∈ P`: derivability
*targets* carry no blanket membership premise, and `imp_elim` — which has no membership premise at
all — derives `.falsum` from `φ.imp .falsum` and `φ`.

The tempting misreading is to treat the membership premise of `falsum_elim` as guarding its
hypothesis rather than its conclusion, and conclude that the carrier must distinguish `.falsum`.
It must not.

**The structural reason.** Across the whole inductive, a membership premise appears exactly where a
rule's *conclusion* is a formula not already known to be permitted — the introduction rules, plus
`falsum_elim` and `em`, whose conclusions are arbitrary. The eliminations whose conclusion is a
component of something already derived (`imp_elim`, `not_not_elim`, `iInf_elim`, `iSup_elim`,
`all_elim`) carry none. So membership guards conclusions, never hypotheses — which is precisely why
no distinguished element is needed in the carrier.
