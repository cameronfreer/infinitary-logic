> **STATUS: COMPLETED (2026-07-10).** Every stage of this plan landed, through commits
> `bcf7f85..62b3872` and the follow-up sublanguage/endpoint commits: the negative-`iInf`
> completion repair, tuple uniformity, the schema formula API, the restricted truth lemma,
> the ΓEMlocal sequence bridge, full indiscernibility + `TailTemplateOmegaWitnessed`, 5c seed
> facts, the §8 Skolem-universality mixin refactor, the §9 wiring, and the two-sorted
> generated-sublanguage endpoint. The definitive theorem is `morley_hanf`
> (`Conditional/MorleyHanfSchemaDischarge.lean`). Archived as the design record; the
> authoritative 5b-1 review is `docs/schema-5b1-equalizer-proof.md`.

# Schema checkpoint 5b: execution plan and verified proof kernels

Date: 2026-07-10  
Audited HEAD: `3db339e`  
Lean sources changed during this audit: none

## Executive verdict

Checkpoint 5a is sound and the tuple-uniformity idea is correct. The fastest honest route to 5b is still the schema completion/term-model route, but one prerequisite was missing from checkpoint 3c: the completion witnesses a positive `iSup`, but it does not witness a **negative `iInf`**. That is not optional. Without a fixed negative conjunct, the proposed restricted truth lemma can fail by witness drift.

The missing rule is already available as

```lean
MarkerHenkinConsistent.neg_iInf_choice
```

in `Methods/MarkerStage.lean`. I tested a symmetric replacement for `stageStep` using that rule. It compiles with no diagnostics. The repair is small and should be committed before the truth lemma.

After that repair, the route is:

1. symmetric completion (`iSup` positive witness and `iInf` negative witness);
2. finite tuple interpolation and `schemaCompletionTheory_tuple_uniform`;
3. a general schema-formula sentence and its source-semantics bridge;
4. a staged, family-restricted truth lemma for the schema term model;
5. full indiscernibility of `schemaSeq` and `TailTemplateOmegaWitnessed`;
6. a small abstraction of the local-Skolem universality assumption, so the existing arbitrary-order local-EM construction can use `schemaTermStructure` as its source structure;
7. Morley-seed agreement and the existing generated-sublanguage wrapper.

The main new result from this audit is that the two apparently risky mathematical kernels—the negative-`iInf` completion step and the arbitrary-constant Skolem step—both elaborate against the current project API.

## Current branch and validation

The worktree was clean at the start of the audit. The relevant commits are:

```text
3db339e SchemaTermModel docstring refresh
d8a2b60 checkpoint 5a quotient model and atomic API
99ce880 sigma-generalization and equality laws
cf8a16c equality-interface foundation
a73cc5e checkpoint 3c completion/spec
```

Both builds passed before this note was written:

```bash
lake build
lake build InfinitaryLogicWIP
```

All experiments described as “LSP-checked” below were run with the non-writing Lean LSP `lean_run_code` facility. No `.lean` file was modified.

## 1. Repair checkpoint 3c first: negative conjunction witnesses

### Why the current completion is insufficient

The current `stageStep` in `Methods/SchemaCompletion.lean` records

```lean
(positive ∧ positive-iSup-witnessed) ∨ negative
```

and its negative branch merely inserts `(ρ n).1.not`. Suppose that `(ρ n).1 = iInf φs`. At the limit theory it is then possible, in principle, to have

```text
¬(⋀ i, φs i) ∈ T
φs 0 ∈ T
φs 1 ∈ T
φs 2 ∈ T
...
```

while every finite fragment remains Marker-consistent: a body for a finite fragment can falsify a component not mentioned by that fragment. The failing component can drift with the body. Finite consistency alone therefore cannot extract a fixed `k` with `¬φs k ∈ T`.

This is precisely the direction needed to prove the term-model implication

```text
(∀ i, termModel ⊨ φs i)  →  termModel ⊨ ⋀ i, φs i.
```

It is also exactly the `iInf_witnessed` field of `TailTemplateOmegaWitnessed`.

### Literature check

This is not an extra strengthening invented for Lean. Marker’s consistency-property definition has separate conjunction and disjunction clauses: positive conjunctions admit every component, while positive disjunctions choose one component. In the truth-lemma negation cases, a negated conjunction is normalized to a disjunction of negated components and therefore must choose a fixed component. See Definition 4.1 and the model-existence truth lemma in Marker’s notes, especially C3/C4 and the negated-conjunction case on pp. 38–42:

- <https://homepages.math.uic.edu/~marker/math512-F13/inf.pdf>

Marker’s Hanf-number proof in §5.2 then uses finite Marker/ER certification to build a model containing indiscernibles, rather than attempting to extract a fully indiscernible sequence from one source model. That matches the project’s present schema/consistency-property reshape; see pp. 53–57 of the same notes.

Keisler’s classical organization also separates the Henkin construction from “Skolem functions and indiscernibles” and the Hanf-number argument; the table of contents and preface are visible in the publisher preview:

- <https://api.pageplace.de/preview/DT0400.9780080954752_A23536582/preview-9780080954752_A23536582.pdf>

### Exact repair shape

Change the decision record returned by `stageStep` to

```lean
(((ρ n).1 ∈ G ∧
    ∀ φs, (ρ n).1 = BoundedFormulaω.iSup φs → ∃ k, φs k ∈ G) ∨
  ((ρ n).1.not ∈ G ∧
    ∀ φs, (ρ n).1 = BoundedFormulaω.iInf φs → ∃ k, (φs k).not ∈ G))
```

The positive branch stays as it is. In the negative branch, after obtaining

```lean
have hneg :=
  (MarkerHenkinConsistent.extension Fp.2 (ρ n).1 (ρ n).2).resolve_left hpos
```

split on whether `(ρ n).1` is an `iInf`. In the shaped case, use:

```lean
have hφs : (ρ n).1 = BoundedFormulaω.iInf (Classical.choose hInf) :=
  Classical.choose_spec hInf
have hmem : (BoundedFormulaω.iInf (Classical.choose hInf)).not ∈
    insert (ρ n).1.not Fp.1 :=
  congrArg BoundedFormulaω.not hφs ▸ Finset.mem_insert_self _ _
have hk := Classical.choose_spec
  (MarkerHenkinConsistent.neg_iInf_choice hneg hmem)
set k := Classical.choose
  (MarkerHenkinConsistent.neg_iInf_choice hneg hmem)
```

and return

```lean
insert (Classical.choose hInf k).not (insert (ρ n).1.not Fp.1)
```

with the same constructor-injectivity argument used by the current positive `iSup` branch, replacing `iSup.injEq` by `iInf.injEq`.

This complete balanced `stageStep` definition was LSP-checked and compiled with no diagnostics.

Then add the projection theorem

```lean
theorem schemaCompletionStage_neg_iInf_witness
    (n : ℕ) {φs : ℕ → ((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω}
    (hiInf : (ρ n).1 = BoundedFormulaω.iInf φs)
    (hneg : (ρ n).1.not ∈ (schemaCompletionStage ρ hM (n + 1)).1) :
    ∃ k, (φs k).not ∈ (schemaCompletionStage ρ hM (n + 1)).1
```

Its proof is the exact mirror of `schemaCompletionStage_witness`: project the negative witness record; in the positive branch contradict stage consistency with `markerHenkinConsistent_not_mem_and_not_mem`. The projection proof also LSP-checks against the tested balanced record shape.

Finally add a theory-level wrapper. The most reusable narrow statement is:

```lean
theorem schemaCompletionTheory_neg_iInf_witness_of_universe
    (τ : FSentence (L'' := localColim s₀) (J := ℕ))
    (hτ : τ ∈ schemaFSentenceUniverse s₀)
    {φs : ℕ → ((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω}
    (hiInf : τ.1 = BoundedFormulaω.iInf φs)
    (hneg : τ.1.not ∈ schemaCompletionTheory (schemaEnumeration s₀) hM) :
    ∃ k, (φs k).not ∈ schemaCompletionTheory (schemaEnumeration s₀) hM
```

The proof should copy the enumeration/stage argument in `schemaCompletionTheory_iSup_witness_localColim`. Do not try to derive this from finite consistency after the theory has been formed; that is exactly where drift occurs.

It is optional to add this field to `SchemaCompletionTheorySpec`. A standalone theorem minimizes API churn and is enough for 5b.

## 2. Finite tuple interpolation

### Statement that already compiles

The following shape was proved axiom-free in an LSP experiment importing only `SchemaTermModel`:

```lean
theorem exists_schema_interpolation
    {M D : Type} [LinearOrder M] [LinearOrder D] [Infinite D]
    {m : ℕ} (S : Finset ℕ) (e : D ↪o M)
    (t t' : Fin m ↪o ℕ)
    (ht : ∀ i, t i ∈ S) (ht' : ∀ i, t' i ∈ S)
    (dflt : M) :
    ∃ σ₁ σ₂ : ℕ → M,
      StrictMonoOn σ₁ ↑S ∧ (∀ j ∈ S, σ₁ j ∈ Set.range e) ∧
      StrictMonoOn σ₂ ↑S ∧ (∀ j ∈ S, σ₂ j ∈ Set.range e) ∧
      ∀ i, σ₁ (t i) = σ₂ (t' i)
```

The tested construction is finite and elementary:

1. Rank `t` and `t'` inside `S`, obtaining two embeddings `p p' : Fin m ↪o Fin S.card`.
2. For an anchor embedding `p`, map `j : Fin S.card` to

   ```text
   (# anchors below j) * (S.card + 1)
     + (if j is an anchor then S.card else j.val).
   ```

3. This map is strictly increasing. Its value at the `i`th anchor is

   ```text
   i * (S.card + 1) + S.card,
   ```

   independently of whether the anchor embedding is `p` or `p'`.
4. Regard the codes as an order embedding into

   ```lean
   Fin ((m + 1) * (S.card + 1))
   ```

   and embed that finite order into `D` with `exists_orderEmb_fin`.
5. Feed the two resulting support embeddings to `tupleInterp`; compose with `e`.

The helper declarations used in the checked proof were:

```text
schemaAnchorRank
schemaAnchorCode
schemaAnchorCode_apply
schemaAnchorCode_strictMono
schemaAnchorCode_lt
schemaAnchorOrderEmb
schemaAnchorOrderEmb_agree
schemaTupleRank
schema_orderEmbOfFin_tupleRank
```

Keep these private unless another checkpoint genuinely consumes them.

### Important support detail

The Marker body’s original support need not contain every entry of `t` or `t'`: a variable can be syntactically unused in `ψ`. Before interpolating, enlarge the body support to

```lean
S' := (S ∪ Finset.univ.image t) ∪ Finset.univ.image t'
```

using `MarkerHenkinBody.enlarge_support`. Both tuple ranges are then contained in `S'`, and both interpolated maps are admissible for the enlarged body.

## 3. Tuple sign-uniformity

Use a local abbreviation for the actual completed sentence:

```lean
private abbrev schemaLift {m : ℕ}
    (ψ : (localColim s₀).BoundedFormulaω Empty m)
    (t : Fin m ↪o ℕ) :=
  (Lomega1omegaTemplate.templateSentence ψ t).mapLanguage
    (((localColim s₀)[[ℕ]]).lhomWithConstants ℕ)
```

and a one-line universe-membership constructor:

```lean
private theorem schemaLift_mem_universe
    (hψ : (⟨m, ψ⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓEMlocal s₀)
    (t : Fin m ↪o ℕ) :
    (⟨schemaLift ψ t, hasFiniteConstSupport_mapLanguage_templateSentence _ _⟩ :
      FSentence (L'' := localColim s₀) (J := ℕ)) ∈ schemaFSentenceUniverse s₀ :=
  Set.mem_biUnion hψ ⟨t, rfl⟩
```

Target theorem:

```lean
theorem schemaCompletionTheory_tuple_uniform
    {m : ℕ} (ψ : (localColim s₀).BoundedFormulaω Empty m)
    (hψ : (⟨m, ψ⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓEMlocal s₀)
    (t t' : Fin m ↪o ℕ) :
    schemaLift ψ t ∈ schemaCompletionTheory (schemaEnumeration s₀) hM ↔
      schemaLift ψ t' ∈ schemaCompletionTheory (schemaEnumeration s₀) hM
```

The exact proof shape was LSP-checked:

1. Prove a directional `transfer u v`.
2. Ask `complete_on_universe` for the sign of `schemaLift ψ v`.
3. If positive, finish.
4. If negative, form

   ```lean
   F := {schemaLift ψ u, (schemaLift ψ v).not}
   ```

   and use `finite_consistent`—not `exists_body_of_subset`—to retain the full `MarkerHenkinBody` universal quantifier.
5. Obtain one body level and its large order embedding `e`.
6. Enlarge its support by both tuple ranges.
7. Apply `exists_schema_interpolation` to obtain `σ₁` and `σ₂` with

   ```text
   σ₁ ∘ u = σ₂ ∘ v.
   ```

8. Apply the body once to `σ₁` and once to `σ₂`. The two Henkin interpretations may differ; that is harmless because the lifted template sentences contain no added Henkin constants.
9. Rewrite both facts with `realizeWith_templateSentence` and `realizeWith_not`. Their assignments to `ψ` are equal, giving a contradiction.
10. Apply `transfer` in both directions.

Do not attempt to find one strict map identifying both tuple images. Usually no such map exists. The proof fundamentally uses two admissible skeleton interpretations of the same universal Marker body.

The tuple-uniformity LSP test used an isolated `axiom` only to stand in for the separately LSP-proved interpolation theorem because `lean_run_code` calls do not persist declarations. The interpolation proof itself compiled axiom-free; production code must use it directly.

## 4. General schema-formula sentences

The restricted truth lemma becomes much cleaner if equality/relation sentences are treated as special cases of one formula-application encoding.

```lean
private def schemaFormulaSentence {n : ℕ}
    (φ : (localColim s₀).BoundedFormulaω Empty n)
    (ts : Fin n → (localColim s₀)[[ℕ]].Term Empty) :
    ((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω :=
  (Lomega1omegaTemplate.templateSentence
      (locDeForm (localColim s₀) ℕ (schemaRelSupport ts) φ ts
        (locJSupport_subset_schemaRelSupport ts))
      ((schemaRelSupport ts).orderEmbOfFin rfl)).mapLanguage
    (((localColim s₀)[[ℕ]]).lhomWithConstants ℕ)
```

Here `schemaRelSupport` is already the correct common-support operation for an arbitrary finite term tuple; it need not be duplicated under a new name.

### Universe membership: LSP-checked

```lean
theorem schemaFormulaSentence_mem_universe {n : ℕ}
    {φ : (localColim s₀).BoundedFormulaω Empty n}
    (hφ : (⟨n, φ⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓlocalColim s₀)
    (ts : Fin n → (localColim s₀)[[ℕ]].Term Empty) :
    (⟨schemaFormulaSentence φ ts,
        hasFiniteConstSupport_mapLanguage_templateSentence _ _⟩ :
      FSentence (L'' := localColim s₀) (J := ℕ)) ∈ schemaFSentenceUniverse s₀ := by
  apply Set.mem_biUnion
    (locDeForm_mem_ΓEMlocal ℕ s₀ (schemaRelSupport ts) hφ ts
      (locJSupport_subset_schemaRelSupport ts))
  exact ⟨(schemaRelSupport ts).orderEmbOfFin rfl, rfl⟩
```

The explicit argument order of `locDeForm_mem_ΓEMlocal` is `J`, `s₀`, `S`, then the formula membership.

### Source-semantics bridge: LSP-checked

The following proof compiled with no diagnostics:

```lean
omit [LinearOrder M] [WellFoundedLT M] in
theorem realize_schemaFormulaSentence_iff
    (σ h : ℕ → M) {n : ℕ}
    (φ : (localColim s₀).BoundedFormulaω Empty n)
    (ts : Fin n → (localColim s₀)[[ℕ]].Term Empty) :
    realizeWith σ h (schemaFormulaSentence φ ts)
        (Empty.elim : Empty → M) Fin.elim0 ↔
      letI : (constantsOn ℕ).Structure M := constantsOn.structure σ
      φ.Realize (Empty.elim : Empty → M)
        (fun i => (ts i).realize (Empty.elim : Empty → M)) := by
  letI : (constantsOn ℕ).Structure M := constantsOn.structure σ
  rw [schemaFormulaSentence, realizeWith_templateSentence, locDeForm, canonDeForm,
    BoundedFormulaω.realize_relabel_sumInr_zero]
  simp only [Formulaω.Realize, BoundedFormulaω.realize_subst]
  refine (realize_openBounds φ _).trans ?_
  apply iff_of_eq
  congr 1
  funext i
  exact locDeTermFin_realize_constInterp_nat σ (ts i)
    (locJSupport_subset_schemaRelSupport ts i)
```

This is the semantic engine for the entire truth lemma. It also gives a short route to all propositional closure facts: if a combination of signs were impossible in an ordinary source structure, `finite_consistent` supplies a body realizing that impossible combination.

The encoding distributes definitionally over `imp`, `iSup`, and `iInf`; those `rfl` equalities were LSP-checked. The `all` case changes the term tuple/support and should be related semantically rather than forced into a definitional equality.

### Semantic sign transport

Add one general helper:

```lean
theorem schema_mem_iff_of_semantic_iff
    (ψ) (hψ : ⟨m, ψ⟩ ∈ ΓEMlocal s₀) (t : Fin m ↪o ℕ)
    (χ) (hχ : ⟨n, χ⟩ ∈ ΓEMlocal s₀) (u : Fin n ↪o ℕ)
    (hsem : ∀ σ h,
      realizeWith σ h (schemaLift ψ t) Empty.elim Fin.elim0 ↔
      realizeWith σ h (schemaLift χ u) Empty.elim Fin.elim0) :
    schemaLift ψ t ∈ T ↔ schemaLift χ u ∈ T
```

This exact pattern compiled. Each direction decides the target sentence. If the target has the wrong sign, `exists_body_of_subset` realizes the source sentence and the negated target in one body, contradicting `hsem`.

Use this helper for support changes, canonical deForms, and normalization to the atomic API. Do not repeatedly re-prove those transports by quotient induction.

## 5. Completion witnesses for canonical deForms

`TailTemplateOmegaWitnessed` is stated for

```lean
canonDeForm (localColim s₀) (iSup φs) g
canonDeForm (localColim s₀) (iInf φs) g
```

rather than the current direct `templateSentence (iSup φs) t` wrapper.

The positive theorem

```lean
schemaCompletionTheory_iSup_witness_canonDeForm
```

was LSP-checked by copying the enumeration/stage proof of `schemaCompletionTheory_iSup_witness_localColim`. The needed membership is

```lean
canonDeForm_mem_ΓEMlocal hmem g
```

and the distribution over `iSup` is `rfl`.

After the stage repair, add the exact negative dual:

```lean
schemaCompletionTheory_neg_iInf_witness_canonDeForm
```

with conclusion

```lean
∃ k, (schemaLift (canonDeForm (localColim s₀) (φs k) g) t).not ∈ T
```

when the negation of the canonical `iInf` sentence is in `T`.

Do not put these fields into `SchemaCompletionTheorySpec` unless that materially shortens downstream proofs. Standalone theorems are sufficient and avoid changing the already-stable 5a consumers.

## 6. Restricted schema truth lemma

### Scope it to the staged family first

Do not begin with an unrestricted theorem for every formula in `ΓEMlocal`. The clean induction datum already exists:

```lean
ψ : (Llocal s₀ (k + 1)).BoundedFormulaω Empty n
hψ : ⟨n, ψ⟩ ∈ Γlocal s₀ (k + 1)
```

Mirror the organization of `LocalEMContext.truthLemmaStage`, but use membership in `T` in place of eventual deep truth. The target equivalence should be morally:

```text
(ψ mapped to localColim, evaluated in schemaTermStructure on classes of ts)
  ↔
schemaFormulaSentence (ψ mapped to localColim) ts ∈ T.
```

Then add a `truthLemmaStage_of_mem`-style wrapper that lifts a stage-`k` member to `k+1` and rewrites with `mapLanguage_LlocalInclusion_lift`. This avoids writing constructor-inversion lemmas for every colimit formula.

### Induction cases

- `falsum`: positive membership is impossible by a one-sentence source body.
- `equal`: normalize `schemaFormulaSentence` to `schemaEqSentence`; use `schemaTerm_realize_eq_mk` and `SchemaTermCarrier.mk_eq_mk_iff`.
- `rel`: normalize to `schemaRelSentence`; use `schemaTerm_relMap_mk_iff`.
- `imp`: use completeness on the child/universe sentences and a finite-body contradiction for the impossible sign combinations.
- `iSup`:
  - a true component implies positive `iSup` by a body contradiction against negative `iSup`;
  - positive `iSup` yields a positive component by `schemaCompletionTheory_iSup_witness_canonDeForm`.
- `iInf`:
  - positive `iInf` implies every component is positive by a one-component body contradiction;
  - if every component is positive but `iInf` is negative, the new fixed negative-component witness contradicts the corresponding positive component.
- `all`:
  - positive `all` implies every term instance by a source-semantic contradiction;
  - negative `all` supplies a fixed local-Skolem witness term. Show the body is negative at that term, then use the induction hypothesis to refute universal truth in the quotient.

The `iInf` case is why the checkpoint-3c repair must precede this theorem.

### Arbitrary-constant Skolem universality: LSP-checked

The existing `locSkWitness_universal` is stated using `locDeepInterp`, but the schema truth lemma receives an arbitrary Marker-body interpretation `σ`. The required generalization does not need interpolation or a new axiom. The following theorem compiled with no diagnostics:

```lean
theorem locSkWitness_universal_constInterp_nat
    (s₀ : LocalStage) {M : Type} [s₀.Lang.Structure M] [Nonempty M]
    (σ : ℕ → M) {k n : ℕ}
    {ψ : (Llocal s₀ k).BoundedFormulaω Empty (n + 1)}
    (h : (⟨n, .all ψ⟩ : Σ n, (Llocal s₀ k).BoundedFormulaω Empty n) ∈ Γlocal s₀ k)
    (ts : Fin n → (localColim s₀)[[ℕ]].Term Empty) :
    letI : (localColim s₀).Structure M := localColimStructure s₀
    letI : (constantsOn ℕ).Structure M := constantsOn.structure σ
    (ψ.mapLanguage (LlocalInclusion s₀ k)).Realize Empty.elim
        (Fin.snoc (fun i => (ts i).realize Empty.elim)
          ((locSkWitnessTerm s₀ ℕ h ts).realize Empty.elim)) →
      ∀ x : M,
        (ψ.mapLanguage (LlocalInclusion s₀ k)).Realize Empty.elim
          (Fin.snoc (fun i => (ts i).realize Empty.elim) x) := by
  letI : (localColim s₀).Structure M := localColimStructure s₀
  letI : (Llocal s₀ k).Structure M := localStageStructure s₀ k
  letI : (constantsOn ℕ).Structure M := constantsOn.structure σ
  simp only [realize_map_LlocalInclusion]
  intro hψw x
  by_contra hcon
  have hex : ∃ b, (ψ.not).Realize Empty.elim
      (Fin.snoc (fun i => (ts i).realize Empty.elim) b) :=
    ⟨x, by rw [BoundedFormulaω.realize_not]; exact hcon⟩
  have hspec : (ψ.not).Realize Empty.elim
      (Fin.snoc (fun i => (ts i).realize Empty.elim)
        (Structure.funMap
          (L := localSkolem (Llocal s₀ k) (skolemNeed (Γlocal s₀ k)))
          (skolemNeedSymbol h) (fun i => (ts i).realize Empty.elim))) :=
    localSkolem_funMap_spec (skolemNeedSymbol h) _ hex
  rw [show Structure.funMap
        (L := localSkolem (Llocal s₀ k) (skolemNeed (Γlocal s₀ k)))
        (skolemNeedSymbol h) (fun i => (ts i).realize Empty.elim)
      = (locSkWitnessTerm s₀ ℕ h ts).realize Empty.elim by
        rw [locSkWitnessTerm, Term.realize_func]
        rfl,
    BoundedFormulaω.realize_not] at hspec
  exact hspec hψw
```

This theorem should live near the schema truth lemma unless the arbitrary-constant form is immediately reused elsewhere.

### Extending from `ΓlocalColim` to `ΓEMlocal`

After the staged theorem, expose the formula-realization/membership bridge for the four summands of

```lean
ΓEMlocal = ΓlocalColim ∪ canonEqAtoms ∪ canonRelAtoms ∪ canonDeForms ΓlocalColim.
```

Use:

- the staged wrapper for `ΓlocalColim`;
- the atomic API for `canonEqAtoms` and `canonRelAtoms`;
- `realize_canonDeForm` plus `schema_mem_iff_of_semantic_iff` for `canonDeForms`.

For a canonical deForm, unpack its base formula `φ ∈ ΓlocalColim` and term tuple `g`, compose `g` with the current closed argument terms, and reduce to the already-proved `ΓlocalColim` case. This is preferable to a second formula induction, especially in the `all` case where the base membership carries the correct local-Skolem symbol.

The only part of this reduction not yet LSP-tested end-to-end is the exact `Term.subst`/language-map expression for composing `g` with closed `(localColim s₀)[[ℕ]]` terms. The semantic statement is already supplied by `realize_canonDeForm`; treat the term-expression plumbing as the next local elaboration hotspot, not as a mathematical gap.

## 7. Full indiscernibility and omega witnesses

Once the `ΓEMlocal` truth bridge is available, tuple uniformity gives the stronger result

```lean
IsLomega1omegaIndiscernibleOn
  (L := localColim s₀) (schemaSeq hM) (ΓEMlocal s₀)
```

not merely tail indiscernibility. For `ψ ∈ ΓEMlocal` and increasing `t,t'`, rewrite both realizations by the truth bridge and then apply `schemaCompletionTheory_tuple_uniform`. Tail indiscernibility follows immediately, with cutoff `0`.

Build

```lean
TailTemplateOmegaWitnessed s₀ (schemaSeq hM)
```

as follows:

- `iSup_witnessed`: template truth → schema-term realization → positive canonical-deForm membership → positive component membership → component realization → component template truth.
- `iInf_witnessed`: all component template truths → all component memberships. If the conjunction were negative, the new fixed negative-component theorem would contradict the matching positive component. Completeness therefore gives the positive conjunction; rewrite back to template truth.

Do not try to prove `iInf_witnessed` by putting infinitely many positive components into one finite Marker fragment.

## 8. The later integration gate: source-structure abstraction

There is one downstream API mismatch that must not be papered over.

The existing theorems

```lean
LocalEMContext.truthLemmaStage
realize_templateSentence_localEM_iff
LocalEMContext.templateTheoryOn_seed_model
tailTemplateRealizable_of_localEMContext
```

install

```lean
letI : (localColim s₀).Structure M := localColimStructure s₀
```

because their `all` case calls the canonical-source Skolem theorem. In the new construction the source model for the arbitrary-`J` local-EM quotient is

```lean
M := SchemaTermCarrier hM
structure := schemaTermStructure hM,
```

which is not definitionally `localColimStructure s₀`.

The clean repair is an explicit mixin, not a cast or a second copy of the entire truth lemma. Define an assignment-level property saying that every stage-family local-Skolem symbol has the required universal property in the given `localColim` structure. Then:

1. prove it for the canonical `localColimStructure` using `localSkolem_funMap_spec` (the current proof);
2. refactor the existing truth lemma into a core theorem taking this property;
3. keep the current theorem name as a wrapper supplying the canonical proof, so existing clients remain unchanged;
4. prove the property for `schemaTermStructure` from the restricted schema truth lemma;
5. add analogous `_of_skolemUniversal` core wrappers through `realize_templateSentence_localEM_iff`, `templateTheoryOn_seed_model`, and `tailTemplateRealizable_of_localEMContext`.

Keep the mixin independent of `J` and terms. Its field should quantify over a value assignment `xs : Fin n → M` and the interpretation of the mapped `skolemNeedSymbol`. Term evaluation then supplies `xs` in the local-EM truth lemma. This gives the smallest reusable interface and avoids tying the abstraction to `locDeepInterp`.

This refactor is downstream of the 5b truth lemma and should be a separate commit. It is the final structural gate to arbitrary target orders; it does not affect tuple uniformity or construction of `TailTemplateOmegaWitnessed`.

## 9. Final wiring to the Morley–Hanf residual

For an arbitrary target linear order `J`, define a `LocalEMContext` over the schema term source:

```text
source carrier  = SchemaTermCarrier hM
source structure = schemaTermStructure hM
ctx.a            = schemaSeq hM
ctx.Γ            = ΓEMlocal s₀
ctx.hind         = full indiscernibility restricted to a tail
ctx.atom_mem     = locDeEqAtom_mem_ΓEMlocal
ctx.rel_mem      = locDeRelAtom_mem_ΓEMlocal
```

Use `TailTemplateOmegaWitnessed.omegaCompleteForColim` to obtain the existing `OmegaCompleteForColim` input for this context. Feed the schema-source Skolem-universality proof to the generalized local-EM acceptance theorem.

For the Morley seed, prove template agreement only for the two seed entries:

- the original sentence `φ` (arity `0`): a negative completion sign would yield a source body falsifying `φ`, contradicting the source hypothesis;
- disequality (arity `2`): a negative sign would yield a body equating two values of a strictly increasing skeleton interpretation.

This is the schema analogue of `morleySeed_template_agreement`; it is much narrower than agreement on all of `ΓEMlocal`.

Finally reuse the generated-sublanguage/re-expansion pattern already present in `LocalEMOmegaResidual.lean` to remove function-symbol countability from the public Morley–Hanf theorem. Do not add a global countability hypothesis merely to simplify the intermediate statement.

## Recommended commit sequence

### Commit 5b-0 — balanced completion

Files: `Methods/SchemaCompletion.lean`

- make `stageStep` symmetric;
- add `schemaCompletionStage_neg_iInf_witness`;
- add theory-level negative-`iInf` witness wrapper;
- refresh 3c docstrings so they no longer claim only positive `iSup` closure.

Acceptance: default/WIP builds, no new axioms, and the existing `SchemaCompletionTheorySpec` consumers still compile.

### Commit 5b-1 — interpolation and tuple uniformity

Files: `Methods/SchemaTermModel.lean`

- private anchor/interpolation helpers;
- `exists_schema_interpolation`;
- `schemaLift` and universe helper;
- `schemaCompletionTheory_tuple_uniform`.

Acceptance: theorem is schema-universe scoped; proof retains `MarkerHenkinBody` and applies it twice.

### Commit 5b-2 — schema formula API

Files: `Methods/SchemaTermModel.lean`

- `schemaFormulaSentence`;
- universe membership;
- `realize_schemaFormulaSentence_iff`;
- semantic sign transport;
- canonical-deForm `iSup`/negative-`iInf` wrappers.

Acceptance: all bridge theorems are axiom-clean; connective distribution is local and explicit.

### Commit 5b-3 — restricted truth lemma

Files: preferably a new `Methods/SchemaTermTruth.lean`, imported by WIP; keep 5a’s substrate file stable.

- arbitrary-constant local-Skolem universality;
- staged truth lemma;
- colimit/canonical-atom/canonical-deForm wrappers;
- single exported `ΓEMlocal` realization iff membership theorem.

Acceptance: structural induction covers `falsum/equal/rel/imp/all/iSup/iInf`; no unrestricted formula claim.

### Commit 5b-4 — indiscernibility and witnessed template

Files: `Methods/SchemaTermTruth.lean` or a small `Methods/SchemaTermWitness.lean`

- full `ΓEMlocal` indiscernibility of `schemaSeq`;
- `TailTemplateOmegaWitnessed s₀ (schemaSeq hM)`.

Acceptance: both omega clauses proved, no “all/truth lemma” work left hidden in the next commit.

### Commit 5b-5 — generic local-Skolem source interface

Files: `Methods/LocalEMTruth.lean`, `Methods/LocalEMTruthLemma.lean`, `Methods/LocalEMTemplateRealization.lean`

- assignment-level Skolem-universality mixin;
- canonical instance/proof;
- core theorems with explicit mixin;
- compatibility wrappers preserving all current theorem names;
- schema-term-model proof of the mixin.

Acceptance: all existing clients compile unchanged; the generalized core accepts `schemaTermStructure` without casts.

### Commit 5b-6 — residual discharge

Files: schema integration file plus the Conditional-facing bridge only where needed

- arbitrary-`J` context from `schemaSeq`;
- omega-completeness;
- two-entry Morley-seed agreement;
- generated-sublanguage wrapper;
- public `MorleySeedTailTemplateRealizable`, then existing Morley–Hanf consumer.

Acceptance: no false-shaped in-source extraction hypothesis is used; the constructed model is where the indiscernibles live, exactly as in Marker §5.2.

## Proof-engineering traps to avoid

1. **Do not use `exists_body_of_subset` for tuple uniformity.** It chooses one skeleton interpretation and discards body universality.
2. **Do not omit tuple ranges from the enlarged support.** Syntactically unused variables need not occur in the original Marker support.
3. **Do not try to identify two tuples with one strict map.** Use two body applications with equal output tuples.
4. **Do not derive a negative `iInf` component after forming the union theory.** Add the witness at the stage where the negative sign is chosen.
5. **Do not introduce ordinary Henkin witnesses for the `all` case.** The local tower already contains the family-indexed Skolem symbol; use `locSkWitnessTerm`.
6. **Do not import `LocalEMOmegaResidual.lean` merely for `realize_canonDeForm`.** Either move that small generic lemma down to `LocalEMFamily.lean`/a neutral semantic file or reproduce its three-line proof locally. Importing the Conditional-facing file would damage the boundary.
7. **Do not assume the schema term structure is the canonical colimit structure.** Thread the Skolem-universality interface explicitly.
8. **Do not settle for tail indiscernibility if tuple uniformity gives cutoff `0`.** The stronger statement simplifies later uses and documents what the completion actually constructed.

## Validation checklist after every commit

```bash
lake build
lake build InfinitaryLogicWIP
python3 scripts/check_sorry_boundary.py
bash scripts/check_import_boundary.sh
bash scripts/check_local_boundary.sh
```

For new load-bearing theorems, also inspect axioms with Lean LSP `lean_verify` or temporary `#print axioms`. The expected noncomputable foundations are the project’s normal classical/quotient axioms; there should be no declaration-specific `sorryAx`, test `axiom`, or new opaque hypothesis.

The most useful theorem-level checks are:

```text
exists_schema_interpolation
schemaCompletionTheory_tuple_uniform
realize_schemaFormulaSentence_iff
schemaTerm_truthLemmaStage
schemaSeq_indiscernibleOn_ΓEMlocal
schemaTerm_tailTemplateOmegaWitnessed
```

## Bottom line

The tuple-uniformity proof is viable exactly as proposed, including the two-interpretation correction. The project already contains almost all the difficult combinatorics and Marker closure API. The newly discovered blocker is local and repairable: make completion symmetric before asking the term model to respect countable conjunctions. The quantifier case is also viable with the existing local-Skolem machinery; its arbitrary-constant kernel has been checked in Lean. The remaining work is mostly disciplined theorem plumbing and one explicit downstream abstraction of the source Skolem property.
