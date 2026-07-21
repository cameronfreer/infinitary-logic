# López–Escobar, hard direction (#10): statement-and-interface audit (v1)

Pre-implementation audit for issue #10, in the pattern of `docs/wellordering-audit.md` /
`docs/craig-audit.md`. Source: Marker, *Math 512 lecture notes*, Corollary 4.22, Lemma 4.23,
Corollary 4.24, Theorem 4.25 (pp. 47–49), checked against the actual text on 2026-07-21.
Status: **v1, awaiting review — nothing frozen yet, no Lean before the D-points are signed
off.** Per the roadmap, #10 is the sole active proof arc; #30 stays audit-only.

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

### D1 — the PC-class predicate: same-carrier expansions

Marker's `PC` class is "the class of `τ`-reducts of models of `φ'`", i.e. membership of a
`τ`-structure `M` is *∃ an expansion of `M` itself* — **same carrier** — to a `τ'`-structure
modeling `φ'`. Corollary 4.22's disjointness step quantifies over expansions of one common
`M`. **Proposed freeze:** the abstract predicate is

    PCMem (Θ : L'.Sentenceω) (incl : L →ᴸ L') (M) [L.Structure M] : Prop :=
      ∃ inst' : L'.Structure M, (incl.reduct-compatibility with the given L-structure) ∧
        Sentenceω.Realize Θ M (w.r.t. inst')

with reduct-compatibility stated as `incl.reduct M (inst') = inst` (`Structure.ext`-style
equality of instances, as in `reduct_expandSymbStructureBase`), **not** `IsExpansionOn`
alone. Arbitrary-countable-expansion variants are *not* introduced. Flag for review: whether
to package `PCMem` as a structure carrying `inst'` (data) or keep it propositional.

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

**Proposed freeze:** both levels as above; the hard theorem is stated and proved at code
level, `PCMem` appears only inside the disjointness lemma.

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

**Proposed freeze:** exactly this chain, as a standalone reusable Descriptive lemma
("analytic-with-tree normal form"), stated for `StructureSpace L` first (generalization to
zero-dimensional Polish products is *not* required for #10). No lightface/effective content
anywhere — `Θ` is built *classically* from `T` (the Gandy–Harrington lightface obstruction
from the Silver arc does **not** apply here). Flag for review: whether the tree's nodes are
indexed by `ℕ`-length initial segments after fixing an enumeration `e : RelQuery L → ℕ`
(needed anyway for D4's numeral coding — see below), or kept as finite partial functions.
Recommendation: index through `e` immediately; one coding, used twice.

### D4 — witness codes as added relations (relational recoding of `τ*`)

Marker's `τ*` has unary *functions* `s, f, g` and a *constant* `c`; the project's
`StructureSpace` and `craig_pcSeparation_relational` are relational. **Proposed freeze:**
hand-roll a small fixed relational PC vocabulary — do *not* route through the
`graphLanguage` machinery (that relationalizes an arbitrary language's own functions and
drags the term-graph calculus; here the extra symbols are a fixed finite-plus-`S_n` family
independent of `L`):

    PCLang : Language := { relations := C¹ (zero), S² (successor graph), F² (f-graph),
                            G² (g-graph), Sₙ^{2n} (n ≥ 1) }
    L* := L.sum PCLang

`Θ`'s bullets translate with totality/functionality axioms for `S, F, G` and uniqueness for
`C` (finitary, in the pattern of the #8 graph axioms but written directly), and Marker's
numeral terms `sⁱ(c)` become inductively defined **numeral formulas** `Numᵢ(x)`
(`∃`-chains through `S` from the `C`-element). Bullet 3 generalizes from `τ = {R}` to
arbitrary countable relational `L` through the query enumeration `e : RelQuery L → ℕ`
(injective suffices; `Encodable` from the existing `Countable (RelQuery L)` instance): the
conjunction ranges over queries `q = (R, v)`, relating `RelMap R` at the numerals of `v` to
the `F`-value at numeral `e q`. Bullet 1 forces the carrier to be infinite — recorded
explicitly, consumed by D6. All conjunctions are countable (`2^{<ω} × ω^{<ω}`-indexed at
each length, queries, `n`). Flag for review: `Sₙ` arity bookkeeping (`2n`-ary relations mean
the `PCLang` relation family is `ℕ`-indexed at unbounded arities — check
`Countable (Σ l, PCLang.Relations l)` comes out by construction; it does, but the instance
must be written).

### D5 — where isomorphism invariance is consumed

**Exactly twice, both inside Lemma 4.23's converse direction** (once per PC presentation,
D8): from a carrier-`ℕ` model of `Θ` one reads off a path, builds the coded structure `N`
from the path's `f̂`, and the `S`-chain provides a `Language.Equiv` between `N` and the
`τ`-reduct; `IsomorphismInvariant B` (the existing predicate, `LopezEscobarEasy.lean`)
transports `N ∈ B` to the reduct's code. Nowhere else: the separation step and the LS step
never mention invariance. **Proposed freeze:** invariance enters only through the lemma
"`pcClass Θ_B` has as carrier-`ℕ` models exactly the codes of `B`" (one direction analytic
representation, the other direction invariance).

### D6 — the countable-to-arbitrary bridge (#13)

Marker: "since there are no countable structures in `K₀ ∩ K₁`, by Löwenheim–Skolem, `K₀`
and `K₁` are disjoint classes." In-project: suppose `M` (arbitrary) had same-carrier
expansions modeling both `Θ₀` and `Θ₁` — equivalently one `L**`-structure on `M` modeling
`Θ₀ ⊓ Θ₁` over the union language (D8). Take a **countable fragment** containing the
subformulas of `Θ₀ ⊓ Θ₁` and a countable fragment-elementary substructure (#13, closed:
`exists_countable_aElementary_substructure`), which still models `Θ₀ ⊓ Θ₁`; bullet 1 of
either `Θ` forces it infinite; transport along a bijection to carrier `ℕ`; its `L`-reduct
code then lies in `B ∩ (univ ∖ B)` by D5's lemma — contradiction. **Proposed freeze:** the
bridge is one dedicated lemma (`pc_disjoint_of_no_countable_common_model`-shaped), the only
consumer of #13 in the arc; the carrier transport reuses whatever
`Descriptive`/`CountingModels` renaming plumbing exists (check before writing — flag: locate
the existing "transport a countable structure to carrier ℕ" lemma; the Scott/counting files
have one).

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
**Proposed freeze:** consume the relational form exactly as stated (no re-derivation from
`craig_interpolation`); the `Nonempty` side conditions are discharged by bullet 1
(infinite carriers). Flag for review: the `θ₀`-transport composite
(sublanguage → `L`) needs one realization-transfer lemma of the
`realize_restrictSymbols`/`mapLanguage` family — check `CraigSublanguage.lean` exports it in
the needed direction before writing a new one.

### D8 — the two PC presentations

`B` invariant Borel ⇒ `B` and `Bᶜ` invariant analytic (`IsomorphismInvariant.compl` exists,
`Descriptive/InvariantMeasurableSpace.lean`; `MeasurableSet.compl` + `MeasurableSet.analyticSet`
supply the rest). Apply D3+D4 twice:
`Θ₀` for `B` and `Θ₁` for `Bᶜ`, over *disjoint tagged copies* of `PCLang` in
`L** = L.sum PCLang.sum PCLang` (`Θ₀` through `Sum.inl ∘ Sum.inr`-style symbol injections,
`Θ₁` through the other; both reduct to the same `L`). **Proposed freeze:** the presentation
is a single reusable construction `pcSentence (analytic-rep data) : L*.Sentenceω`
instantiated twice via the two tagged inclusions — not two hand-written variants.

### D9 — the coding pilot (before the general theorem)

A compile-gated pilot **before** committing to the full analytic-to-PC unit:

1. `PCLang`, the tagged inclusions, and the countability instances;
2. bullet-1 axioms and numeral formulas `Numᵢ`, with the two realization lemmas in the
   standard model on `ℕ` (`C ↦ {0}`, `S ↦ succ-graph`): `Numᵢ(x) ↔ x = i`, and "every model
   of bullet 1 is infinite with a canonical `(ℕ, 0, succ)`-labeling";
3. the D3 tree lemma on `StructureSpace L` (branch characterization through cylinders).

Acceptance: all three compile axiom-clean with no statement changes to existing files. The
pilot deliberately excludes `S_n`/path bullets — those are mechanical once 2 and 3 stand.

### D10 — compile-gated units and the stop/go criterion

Unit order (each a commit, later units untouched if an earlier one stalls):

1. pilot (D9);
2. `pcSentence` + the two directions of D5's lemma (analytic rep ⇄ carrier-`ℕ` models);
3. D6 disjointness bridge (the only #13 consumer);
4. separation + transport (D7) and the endpoint `lopez_escobar`;
5. the packaged `lopezEscobar_iff` (reverse = existing `lopezEscobar_easy`);
6. only afterward: facade/blueprint/guard sweep, and the `lopezEscobar_action_iff` wrapper
   *only if* #27's `ActionInvariant ↔ IsomorphismInvariant` is already available.

**The crucial gate is D3/D9.3** — the analytic-to-tree normal form against Mathlib's
continuous-image definition — *not* Craig or downward LS (both consumers are ready).
**Stop/go:** if the branch-characterization lemma resists a bounded effort (two focused
sessions), stop and rework the representation layer *before* touching units 2–5; fallback
options, in order: (a) prove the tree normal form as a standalone lemma for countable
products of discrete spaces (still boldface, no effectivity); (b) restate the hard
direction against an explicit closed-projection witness and add the Mathlib-facing
`AnalyticSet → projection` step as its own unit. Abandoning Marker's route for a
Vaught-transform route is **not** on the table at this stage (the issue's route note
stands: the logic-action layer and ∗-transform calculus would be new central pieces).

## 3. Non-goals (recorded to prevent scope creep)

* No `Equiv.Perm ℕ` action layer (#27) and no invariant-σ-algebra packaging (#28) on this
  path; `lopezEscobar_action_iff` is a thin post-#27 corollary.
* No general-language / non-relational wrappers before the countable relational endpoint.
* No Borel-hierarchy induction anywhere (it does not preserve invariance — the route is
  Marker's, through analytic representations).
* No #30 implementation alongside; #33 consumes the endpoint later via its own bridge.
