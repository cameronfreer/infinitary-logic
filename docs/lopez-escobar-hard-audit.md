# López–Escobar, hard direction (#10): statement-and-interface audit (v2)

Pre-implementation audit for issue #10, in the pattern of `docs/wellordering-audit.md` /
`docs/craig-audit.md`. Source: Marker, *Math 512 lecture notes*, Corollary 4.22, Lemma 4.23,
Corollary 4.24, Theorem 4.25 (pp. 47–49), checked against the actual text on 2026-07-21.
Status: **v2, FROZEN per review 2026-07-22**: D1 revised to `IsExpansionOn` (not instance
equality), D3 extended with the `queryCode` closed-embedding gate, D4 reversed to
graph-translation-first (hand-rolled relational vocabulary demoted to fallback), D5/D6
refined, and the unit order restructured with Unit 0 as the stop/go gate. Per the roadmap,
#10 is the sole active proof arc; #30 stays audit-only.

## 1. Source statements (verified against the PDF)

**Corollary 4.22 (PC separation).** Suppose `K₀` and `K₁` are disjoint `PC_ω₁ω`-classes of
`τ`-structures. There is `φ ∈ L_ω₁ω(τ)` such that `M ⊨ φ` for `M ∈ K₀` and `M ⊨ ¬φ` for
`M ∈ K₁`. *Proof:* `τ₀, τ₁ ⊇ τ` with `τ₀ ∩ τ₁ = τ` (WLOG), `Kᵢ` = the `τ`-reducts of models
of `φᵢ ∈ L_ω₁ω(τᵢ)`. Disjointness gives `φ₀ ⊨ ¬φ₁` — "if there is any expansion of `M` that
makes `φ₀` true, then there is no expansion of `M` making `φ₁` true" — and interpolation
yields `φ ∈ L_ω₁ω(τ)` with `φ₀ ⊨ φ` and `φ ⊨ ¬φ₁`.

**Lemma 4.23.** Every invariant `Σ¹₁` subset `A` of `X_τ` is the set of countable models in
a `PC_ω₁ω`-class. *Proof* (for `τ = {R}`, `R` binary; `p : ω² → ω` a pairing; `f_R : ω → 2`
the characteristic code `f_R(p(i,j)) = 1 ↔ R(i,j)`): since `A` is analytic there is a tree
`T ⊆ {(η,ν) : η ∈ 2^{<ω}, ν ∈ ω^{<ω}, |η| = |ν|}` with `(ω,R) ∈ A` iff some `g` makes
`(f_R, g)` a path through `T`. Let `τ* = {s, c, f, g, S_n : n ≥ 1}` — `s, f, g` **unary
functions**, `c` a **constant**, `S_n` a `2n`-ary relation — and `Θ` assert:

1. `s` is one-to-one, every element except `c` has a preimage, no cycles, and
   `∀x ⋁ᵢ s⁽ⁱ⁾(c) = x` — i.e. `(carrier, c, s) ≅ (ω, 0, succ)`;
2. `∀x (f(x) = c ∨ f(x) = s(c))` — `f` is two-valued;
3. `⋀_{i,j} [R(s⁽ⁱ⁾(c), s⁽ʲ⁾(c)) ↔ f(s⁽ᵖ⁽ⁱ,ʲ⁾⁾(c)) = s(c)]` — `f` *is* the code of `R`;
4. `⋀_n ⋀_{(η,ν)}` [`S_n` at the numeral tuple for every `(η,ν) ∈ T` of length `n`, and
   `¬S_n` for every `(η,ν) ∉ T`] — `S_n` is pinned to be exactly `T` at numerals;
5. `⋀_n S_n(f(c), …, f(sⁿ⁻¹(c)), g(c), …, g(sⁿ⁻¹(c)))` — `(f, g)` is a path through `T`.

Forward: `(ω,R) ∈ A` expands to a model of `Θ` (interpret `c = 0`, `s = succ`, `g` the
witness, `S_n = T`). Converse: from `M* ⊨ Θ` with `τ`-reduct `(ω, R)`, read off
`f(sⁱ(c)) = s^{η(i)}(c)` and `g(sⁱ(c)) = s^{ν(i)}(c)`, take the union path `(f̂, ĝ)` through
`T`, let `R̂` be the relation coded by `f̂` and `N = (ω, R̂)`; then `N ∈ A`, and "`s` gives an
isomorphism between `N` and `M = (ω,R)`. Thus, **since `A` is invariant**, `M ∈ A`."

**Corollary 4.24.** Disjoint invariant `Σ¹₁` sets are separated by an invariant Borel set.

**Theorem 4.25.** Every invariant Borel subset of `X_τ` is `Mod(φ)` for some
`L_ω₁ω(τ)`-sentence `φ`. *Proof:* `A` and `X_τ ∖ A` are disjoint invariant `Σ¹₁`; take
`PC`-classes `K₀`, `K₁` for them by Lemma 4.23. "Since there are no countable structures in
`K₀ ∩ K₁`, **by Löwenheim–Skolem**, `K₀` and `K₁` are disjoint classes." Corollary 4.22
separates: `A ⊆ Mod(φ)` and `Mod(φ) ∩ (X_τ ∖ A) = ∅`, so `A = Mod(φ)`. (Footnote 8:
alternatively restrict all models of the PC classes to be countable from the start.)

## 2. The ten decision points

### D1 — the PC-class predicate: same-carrier expansions via `IsExpansionOn` [FROZEN, v2]

Marker's `PC` class is "the class of `τ`-reducts of models of `φ'`", i.e. membership of a
`τ`-structure `M` is *∃ an expansion of `M` itself* — **same carrier** — to a `τ'`-structure
modeling `φ'`; same-carrier is already enforced by the types. Corollary 4.22's disjointness
step quantifies over expansions of one common `M`. **Frozen:**

    def PCMem (Θ : L'.Sentenceω) (incl : L →ᴸ L')
        (M : Type) [L.Structure M] : Prop :=
      ∃ inst' : L'.Structure M,
        @incl.IsExpansionOn M _ inst' ∧
        @Sentenceω.Realize L' Θ M inst'

`IsExpansionOn` agrees on every base symbol — exactly the needed reduct condition; equality
of structure instances is stronger, awkward under typeclass elaboration, and unnecessary.
`PCMem` stays **propositional** (a data-bearing structure would complicate set membership
without helping consumers). Arbitrary-countable-expansion variants are *not* introduced.

### D2 — reduct-class semantics on `StructureSpace L`

Two levels, with a compatibility lemma:

* **code level** — for a language inclusion `incl : L →ᴸ L'` between countable relational
  languages, the code-reduct `ρ : StructureSpace L' → StructureSpace L`,
  `ρ c' = fun q => c' (incl-image of q)`; the coded PC class is `ρ '' ModelsOf Θ`. `ρ` is
  continuous (each output coordinate is one input coordinate) — recorded but *not*
  load-bearing: the PC class is analytic, never claimed Borel.
* **abstract level** — `PCMem` of D1, used only in the disjointness/LS step.
* **compatibility** — `c ∈ ρ '' ModelsOf Θ ↔ PCMem Θ incl ℕ` (with `c.toStructure`):
  same-carrier expansion of a code is exactly a code over the expanded language reducting to
  it. This needs decode/encode round-trips on `StructureSpaceOn L' ℕ` — check what
  `Descriptive/StructureSpace.lean` already provides before writing new ones.

**Frozen (approved with D1's revised `PCMem`):** both levels as above; the hard theorem is
stated and proved at code level, `PCMem` appears only inside the disjointness lemma.

### D3 — the analytic representation Mathlib supplies

Mathlib (`MeasureTheory.AnalyticSet`, `Constructions/Polish/Basic.lean`) defines analytic as
**`s = ∅ ∨ ∃ f : (ℕ → ℕ) → α, Continuous f ∧ range f = s`** — a continuous image of Baire
space, *not* a tree/closed-projection normal form. Available: `MeasurableSet.analyticSet`
(Borel ⇒ analytic, `[PolishSpace α]`; the project has `instPolishSpaceStructureSpace`), and
the same for the complement via `MeasurableSet.compl`. **The tree form must be derived
in-project**, in two steps:

1. continuous image → closed graph: `C := {(x, y) | f y = x} ⊆ X × ℕ^ℕ` is closed (`f`
   continuous, `X` T2), and `B = {x | ∃ y, (x,y) ∈ C}` (empty case trivial);
2. closed set → tree of cylinders: with `X = RelQueryOn L ℕ → Bool` carrying the product
   topology over a countable discrete index, basic neighborhoods of `(x,y)` are pairs
   (finite partial information on `x`, initial segment of `y`); define
   `T := {(finite condition pair) | its cylinder meets C}`; then branches of `T` = closure
   of `C` = `C`.

**Frozen (v2), with the query-code closed-embedding gate added before the cylinder tree.**
An injection `RelQuery L → ℕ` alone is not enough: a branch of a tree over raw bit
sequences need not determine an actual structure code (unused coordinates could be
inconsistent). Expose first, via `Encodable.encode` with harmless defaults at numbers that
decode no query:

    queryCode : StructureSpace L → (ℕ → Bool)

and prove: (i) `queryCode` is continuous and injective; (ii) its **range is closed**;
(iii) every query is recovered at its encoded coordinate; (iv) range membership is
characterized by the default/decoding consistency conditions. Then build the cylinder tree
in `(ℕ → Bool) × (ℕ → ℕ)`. The consumer-shaped normal form is approximately

    c ∈ B ↔ ∃ g : ℕ → ℕ, ∀ n, (prefix (queryCode c) n, prefix g n) ∈ T n

with the empty analytic set served by a tree with no positive-length branch. This whole
package — `queryCode` gate + tree normal form — is **Unit 0, the actual stop/go gate**
(D10). Standalone reusable Descriptive lemmas, stated for `StructureSpace L` first
(zero-dimensional Polish generality is *not* required). No lightface/effective content
anywhere — `Θ` is built *classically* from `T` (the Gandy–Harrington lightface obstruction
from the Silver arc does **not** apply here).

### D4 — witness language: graph translation FIRST, hand-rolled relational fallback [REVERSED, v2]

Marker's `τ*` has unary *functions* `s, f, g` and a *constant* `c`; the project's
`StructureSpace` and `craig_pcSeparation_relational` are relational. **Frozen (reversing
v1's recommendation): Marker's functional language is precisely what the completed Craig
Layer 3 was built to relationalize — try the existing graph translation first.**

1. A small **functional witness language** `W` with `c, s, f, g` and relational `Sₙ`
   (`2n`-ary).
2. **Actual numeral terms** `sⁱ(c)` — `Θ` becomes almost verbatim Marker.
3. A common tagged language `K := L.sum (W₀.sum W₁)` (two tagged witness copies, D8).
4. Each functional PC sentence maps into `K`.
5. Apply `relationalizeFormula` plus `graphAxioms` for the functions used by that side.

Existing files already provide nested-term flattening, graph axioms, reconstruction, exact
occurrence identities, and back-translation: `Methods/Interpolation/Relationalize.lean`,
`GraphAxioms.lean`, `GraphReconstruction.lean`, `BackTranslate.lean`. With tagged witness
copies, the occurrence intersection should contain only the graph-language images of base
`L`-relations — exactly the sharp-intersection calculation already solved during Craig.

**Timeboxed spike (Unit 1):** define `W` and the numeral terms; map the two copies into
`K`; relationalize bullet 1; prove the intersection of the two translated occurrence sets
contains no witness symbols. **If the spike fails on dependent language bookkeeping**, fall
back to v1's hand-rolled relational vocabulary (fixed `PCLang` with graph relations
`C¹/S²/F²/G²/Sₙ^{2n}`, totality/functionality axioms, inductively defined numeral
*formulas*) — but fresh numeral-formula and graph-functionality machinery is **not** the
first choice.

Independent of the branch taken: bullet 3 generalizes from `τ = {R}` to arbitrary countable
relational `L` through the same `Encodable` query coding as D3's `queryCode` (one coding,
used twice); bullet 1 forces the carrier to be infinite — recorded explicitly, consumed by
D6; all conjunctions are countable (`2^{<ω} × ω^{<ω}`-indexed at each length, queries,
`n`); and the `Countable (Σ l, W.Relations l)` / functions instances must be written for
the `ℕ`-indexed unbounded-arity `Sₙ` family.

### D5 — where isomorphism invariance is consumed

**Exactly twice, both inside Lemma 4.23's converse direction** (once per PC presentation,
D8): from a carrier-`ℕ` model of `Θ` one reads off a path, builds the coded structure `N`
from the path's `f̂`, and the `S`-chain provides a `Language.Equiv` between `N` and the
`τ`-reduct; `IsomorphismInvariant B` (the existing predicate, `LopezEscobarEasy.lean`)
transports `N ∈ B` to the reduct's code. Nowhere else: the separation step and the LS step
never mention invariance. **Frozen (refined):** invariance enters only through **one
generic converse lemma** — "`pcClass Θ` has as carrier-`ℕ` models exactly the codes of the
represented set" (one direction analytic representation, the other direction invariance) —
**instantiated twice** (at `B` and at `Bᶜ`), never re-proved.

### D6 — the countable-to-arbitrary bridge (#13)

Marker: "since there are no countable structures in `K₀ ∩ K₁`, by Löwenheim–Skolem, `K₀`
and `K₁` are disjoint classes." In-project: suppose `M` (arbitrary) had same-carrier
expansions modeling both `Θ₀` and `Θ₁` — equivalently one `L**`-structure on `M` modeling
`Θ₀ ⊓ Θ₁` over the union language (D8). Take a **countable fragment** containing the
subformulas of `Θ₀ ⊓ Θ₁` and a countable fragment-elementary substructure (#13, closed:
`exists_countable_aElementary_substructure`), which still models `Θ₀ ⊓ Θ₁`; bullet 1 of
either `Θ` forces it infinite; transport along a bijection to carrier `ℕ`; its `L`-reduct
code then lies in `B ∩ (univ ∖ B)` by D5's lemma — contradiction. **Frozen (refined):** the
bridge is one dedicated lemma (`pc_disjoint_of_no_countable_common_model`-shaped), the only
consumer of #13 in the arc. The carrier transport needs **no new framework**: Mathlib's
`nonempty_equiv_of_countable` (instance, `Logic/Denumerable.lean`; `Countable` + `Infinite`
on both sides) supplies the bijection, and the repository's `BoundedFormulaω.realize_equiv`
(`Lomega1omega/Theory.lean`) transports realization along it.

### D7 — orientation of `craig_pcSeparation_relational`

Verified against `Methods/Interpolation/CraigSeparation.lean`: from
`Sentenceω.Entails ψ₁ ψ₂.not` it produces `θ₀` over
`symbSublang (ψ₁.functionsIn ∩ ψ₂.functionsIn) (ψ₁.relationsIn ∩ ψ₂.relationsIn)` with

* every nonempty model of `ψ₁` satisfies `θ₀` through the sublanguage **reduct**, and
* every nonempty model of `ψ₂` satisfies `¬θ₀` through the reduct.

For #10: `ψ₁ := Θ₀`, `ψ₂ := Θ₁` over the union language `L** := L.sum PCLang.sum PCLang`
(two *tagged* copies, D8), `Entails Θ₀ Θ₁.not` = D6. The intersection occurrence sets land
inside the `L`-summand by construction (the two `PCLang` copies are disjoint summands), so
`θ₀` lives over a sublanguage of `L`-symbols; a final `mapLanguage` along
`symbSublangIncl`-then-`Sum.inl` returns it to `L.Sentenceω`, and the two bullets become
`B ⊆ ModelsOf θ` and `ModelsOf θ ∩ Bᶜ = ∅` at code level through D2's compatibility.
**Frozen (approved):** consume the relational form exactly as stated (no re-derivation from
`craig_interpolation`); the `Nonempty` side conditions are discharged by bullet 1
(infinite carriers). Flag for review: the `θ₀`-transport composite
(sublanguage → `L`) needs one realization-transfer lemma of the
`realize_restrictSymbols`/`mapLanguage` family — check `CraigSublanguage.lean` exports it in
the needed direction before writing a new one.

### D8 — the two PC presentations

`B` invariant Borel ⇒ `B` and `Bᶜ` invariant analytic (`IsomorphismInvariant.compl` exists,
`Descriptive/InvariantMeasurableSpace.lean`; `MeasurableSet.compl` + `MeasurableSet.analyticSet`
supply the rest). Apply D3+D4 twice:
`Θ₀` for `B` and `Θ₁` for `Bᶜ`, over the *disjoint tagged witness copies* of D4's common
language `K = L.sum (W₀.sum W₁)` (both reduct to the same `L`). **Frozen (approved):** the
presentation is a single reusable construction `pcSentence (analytic-rep data)` instantiated
twice via the two tagged inclusions — not two hand-written variants.

### D9 — the two gating spikes (before the general theorem)

Two compile-gated spikes, in order, **before** committing to the full analytic-to-PC unit:

* **Unit 0 (the stop/go gate)** — D3's `queryCode` closed embedding (continuity,
  injectivity, closed range, coordinate recovery, range characterization) and the analytic
  tree normal form `c ∈ B ↔ ∃ g, ∀ n, (prefix (queryCode c) n, prefix g n) ∈ T n`, with the
  empty set served by a branchless tree.
* **Unit 1 (the D4 spike, timeboxed)** — the functional witness language `W` with numeral
  terms; the two tagged copies mapped into `K = L.sum (W₀.sum W₁)`; bullet 1
  relationalized through the Craig Layer-3 files; and the proof that the intersection of
  the two translated occurrence sets contains no witness symbols. Failure on dependent
  language bookkeeping ⇒ fall back to the hand-rolled relational vocabulary (D4).

Acceptance: both compile axiom-clean with no statement changes to existing files. The
spikes deliberately exclude the `Sₙ`/path bullets — those are mechanical once both stand.

### D10 — compile-gated units and the stop/go criterion [revised order, v2]

Unit order (each a commit, later units untouched if an earlier one stalls):

0. **`queryCode` closed embedding + analytic tree normal form — the actual stop/go gate**;
1. functional witness language + the graph-relationalization intersection spike (D4);
2. the full functional `Θ` and its relationalized PC sentence (`pcSentence`, D8);
3. carrier-`ℕ` correctness — D5's generic converse lemma, invariance only in the converse;
4. abstract `PCMem` (D1) and the #13 disjointness bridge (D6);
5. Craig separation, transport back to `L` (D7), and the endpoint `lopez_escobar`;
6. both packaged equivalences — `lopezEscobar_iff` (reverse = existing `lopezEscobar_easy`)
   and `lopezEscobar_action_iff` (the #27 wrapper `actionInvariant_iff_isomorphismInvariant`
   already exists, `Descriptive/LogicAction.lean`);
7. facade, blueprint, guards, and publication sweep.

**Stop/go (Unit 0):** if the `queryCode`/branch-characterization package resists a bounded
effort (two focused sessions), stop and rework the representation layer *before* touching
units 1–6; fallback options, in order: (a) prove the tree normal form as a standalone lemma
for countable products of discrete spaces (still boldface, no effectivity); (b) restate the
hard direction against an explicit closed-projection witness and add the Mathlib-facing
`AnalyticSet → projection` step as its own unit. Abandoning Marker's route for a
Vaught-transform route is **not** on the table at this stage (the issue's route note
stands: the logic-action layer and ∗-transform calculus would be new central pieces).

## 3. Non-goals (recorded to prevent scope creep)

* No new `Equiv.Perm ℕ` action work (#27) and no invariant-σ-algebra packaging (#28) on
  this path; `lopezEscobar_action_iff` only composes the endpoint with the existing
  `actionInvariant_iff_isomorphismInvariant`.
* No general-language / non-relational wrappers before the countable relational endpoint.
* No Borel-hierarchy induction anywhere (it does not preserve invariance — the route is
  Marker's, through analytic representations).
* No #30 implementation alongside; #33 consumes the endpoint later via its own bridge.
