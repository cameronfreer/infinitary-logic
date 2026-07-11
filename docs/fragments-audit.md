# Fragments audit: countable fragments, A-elementarity, and genuine downward Löwenheim–Skolem

Statement-and-interface audit for issue #13 (first gate — no Lean definitions precede this
document). Sources: Marker, *Lectures on Infinitary Model Theory* (lecture-notes PDF; §1.1
"Fragments and Downward Löwenheim–Skolem", pp. 7–9), and Keisler–Knight, *Barwise: infinitary
logic and admissible sets* (https://people.math.wisc.edu/~hkeisler/kk2.pdf, §3 p. 14, for the
admissible refinement kept compatible but NOT imported here).

## 1. Verbatim statements

**Marker, Definition 1.16 (formal negation, p. 7).** For each formula φ define ∼φ: (i) for φ
atomic, ∼φ is ¬φ; (ii) ∼(¬φ) is φ; (iii) ∼⋀_{φ∈X} φ is ⋁_{φ∈X} ∼φ and ∼⋁_{φ∈X} φ is
⋀_{φ∈X} ∼φ; (iv) ∼∃vφ is ∀v∼φ and ∼∀vφ is ∃v¬φ. (Exercise 1.17: M ⊨ ¬φ iff M ⊨ ∼φ.)

**Marker, Definition 1.18 (fragment, pp. 7–8).** A set of L_ω₁ω-formulas A is a *fragment* if
there is an infinite set of variables V such that every variable occurring in a member of A is
in V, and: (i) all atomic formulas using only the constant symbols of τ and variables from V
are in A; (ii) if φ ∈ A and ψ is a subformula of φ, then ψ ∈ A; (iii) if φ ∈ A, v is free in φ,
and t is a term with every variable in V, then φ(t/v) ∈ A; (iv) A is closed under ∼; (v) A is
closed under ¬, ∧, ∨, ∃v, ∀v for v ∈ V.

**Marker, Exercise 1.19 (generated fragments, p. 8).** For κ regular (in particular ω₁): a set
T of L_κω-sentences with |T| < κ is contained in a fragment A with |A| < κ; there is a smallest
such fragment. (Exercise 1.20: every formula in a fragment has finitely many free variables.)

**Marker, Theorem 1.22 (Downward Löwenheim–Skolem, p. 8).** Let A be a fragment of L_∞ω whose
formulas have finitely many free variables, M a τ-structure, X ⊆ M. There is N ≺_A M with
X ⊆ N and **|N| ≤ max(|A|, |X|)**. In particular for countable τ and countable A ⊆ L_ω₁ω(τ),
every τ-structure has a countable A-elementary submodel.

**Marker, Exercises 1.23–1.24 (Skolem route, pp. 8–9).** Proof outline: expand to τ* ⊇ τ,
A* ⊇ A with |τ*| = |A*| = |A|, adding for each A*-formula φ(v̄,w) a function symbol f_φ with
M ⊨ ∀v̄(∃w φ(v̄,w) → φ(v̄, f_φ(v̄))); then (b) every τ*-substructure N of M* has N ≺_{A*} M*;
(c) some τ*-substructure contains X with |N| ≤ max(|A*|, |X|). Exercise 1.24: built-in Skolem
functions for A-theories.

**Marker, Exercise 1.27 (chains, p. 9).** A a fragment, (I,<) linear, (M_i : i ∈ I) an
A-elementary chain (M_i ≺_A M_j for i < j), M = ⋃ M_i. Then M_i ≺_A M for all i.

**Keisler–Knight, §3 (p. 14).** For an admissible set 𝔸, the admissible fragment L_𝔸 is the
set of L_∞ω-formulas that are ELEMENTS of 𝔸; closed under finite connectives, finite
quantification, subformulas, and substitution; L_HF = L_ωω, L_HC = L_ω₁ω. (This is #18's
refinement; the present interface must be its degenerate/ordinary case, not vice versa.)

## 2. Translation table

| Book | Repository |
|---|---|
| formula φ(v₁,…,vₙ), variables from V | `φ : L.BoundedFormulaω Empty n` (de Bruijn; the arity is the free-variable interface; Ex 1.20 "finitely many free variables" holds by construction) |
| fragment A (one set of formulas, mixed arities) | `Fragment L` with carrier `toSet : Set (Σ n, L.BoundedFormulaω Empty n)` |
| assignment of elements of N to variables | a tuple `a : Fin n → N` — **parameters are semantic**; no named constants in the carrier (`withConstants` appears only inside witness constructions) |
| M ≺_A N | `AElementary A f` for a substructure inclusion/embedding `f`: truth agreement on all members of A at all tuples |
| ∼ (formal negation) | NOT a primitive: `BoundedFormulaω` has `imp`/`falsum` negation; Marker (iv) is an NNF concern deferred to #14's NNF API. The record does not carry a ∼-closure field. |
| subformula closure (ii) | **component closure**: closure under the constructor components (`imp` → both parts, `all` → body, `iInf`/`iSup` → every component). This is what every induction consumes; "subformula" in the de Bruijn setting IS the component relation. |
| substitution closure (iii) | **omitted from the core record.** Marker needs (iii) because his ≺_A substitutes constants/terms for free variables; with semantic tuple parameters, Tarski–Vaught witnesses are ELEMENTS, not terms, and no syntactic substitution enters the proofs. A substitution-closure mixin can be layered later if a consumer (e.g. #8) needs it. |
| atomic closure (i) | **omitted from the core record** — see §10 (the key decision). |

## 3. Proposed `Fragment` fields

```
structure Fragment (L : Language.{0,0}) where
  toSet : Set (Σ n, L.BoundedFormulaω Empty n)
  imp_left_mem  : ⟨n, φ.imp ψ⟩ ∈ toSet → ⟨n, φ⟩ ∈ toSet
  imp_right_mem : ⟨n, φ.imp ψ⟩ ∈ toSet → ⟨n, ψ⟩ ∈ toSet
  all_mem       : ⟨n, φ.all⟩ ∈ toSet → ⟨n+1, φ⟩ ∈ toSet
  iInf_mem      : ⟨n, .iInf φs⟩ ∈ toSet → ∀ k, ⟨n, φs k⟩ ∈ toSet
  iSup_mem      : ⟨n, .iSup φs⟩ ∈ toSet → ∀ k, ⟨n, φs k⟩ ∈ toSet
```

- **Component direction only.** Explicitly NOT required: that countable families of members
  have their conjunction in the fragment (`closed_iInf`-style fields as in the current
  `AdmissibleFragmentCore` — that direction generally destroys countability and is precisely
  what the #18 corrections flag). Closure under FORMING finite connectives/quantifiers is also
  not needed by the ≺_A/LS/chain inductions and is left out of the core; a `Closed` mixin
  bundling formation closure can be added for consumers that need it (the proof system).
- No `falsum`/`equal`/`rel` fields: atoms have no components.
- Countability is a separate predicate/`Countable`-instance on `toSet`, not a field.

## 4. `AElementary`

For `N ⊆ M` realized as a substructure inclusion (Mathlib `L.Substructure M`, or an embedding
`f : N ↪[L] M` — audit outcome: state for embeddings, specialize to `Substructure.subtype`):

```
def AElementary (A : Fragment L) (f : N ↪[L] M) : Prop :=
  ∀ {n} (φ : L.BoundedFormulaω Empty n), ⟨n, φ⟩ ∈ A.toSet →
    ∀ a : Fin n → N, (φ.Realize Empty.elim (f ∘ a) ↔ φ.Realize Empty.elim a)
```

Direct truth agreement; both directions (the fragment is not assumed ∼-closed, so the iff is
stated, not derived). Basic API: identity, composition/transitivity, transport along
isomorphisms, atomic/quantifier-free agreement for free (embeddings preserve atomics), and
`Theoryω.Model` transport for fragment theories.

## 5. Tarski–Vaught and the witness-closure invariant

**Criterion (fragment-relative, existentials only).** For a substructure N ⊆ M:

> if for every `φ : L.BoundedFormulaω Empty (n+1)` with `⟨n, φ.all⟩ ∈ A.toSet` (the
> fragment-controlled quantified members) and every `a : Fin n → N`,
> `(∃ m : M, ¬φ.Realize Empty.elim (Fin.snoc (incl ∘ a) m)) → (∃ b : N, ¬φ.Realize Empty.elim (Fin.snoc (incl ∘ a) (incl b)))`,
> then N ≺_A M.

(∃-shape via `¬∀¬`; only `all`-members of A control witnesses — `all_mem` supplies the body's
membership for the induction. The induction is on φ ∈ A: atomics free, `imp` by components,
`all` by the criterion + components, `iInf`/`iSup` by `iInf_mem`/`iSup_mem` pointwise.)

**Witness-closure invariant (the Skolem hull).** Following Marker Ex 1.23 but with CHOICE
FUNCTIONS instead of a language expansion: for each ⟨n, φ.all⟩ ∈ A choose (noncomputably) a
witness function `w_φ : (Fin n → M) → M` picking a counterexample to φ when one exists. The
hull of X is the closure of X under (a) ALL language functions of L, and (b) the countably-or-
|A|-many `w_φ`. The invariant: a subset closed under (a) is a substructure; closed additionally
under (b) it satisfies Tarski–Vaught. Marker's τ*-expansion (Ex 1.23) is the same construction
presented syntactically; the repo uses the semantic form and reserves `withConstants` for the
model-existence route already in `ModelTheory/LowenheimSkolem.lean` (which is a DIFFERENT
theorem — countable models for satisfiable sentences via Henkin — and is reused, not replaced).

## 6. Downward Löwenheim–Skolem

**Honest general statement** (the foundational theorem):

```
theorem exists_aElementary_substructure (A : Fragment L) (X : Set M) :
    ∃ N : L.Substructure M, X ⊆ N ∧ AElementary A N.subtype ∧
      Cardinal.mk N ≤ max (max Cardinal.aleph0 (Cardinal.mk X))
        (max (Cardinal.mk A.toSet) (Cardinal.mk (Σ n, L.Functions n)))
```

i.e. **|N| ≤ max(ℵ₀, |X|, |A|, |Σ n, L.Functions n|)**. Only function symbols enlarge the hull
directly (clause (a) of §5); the fragment contributes |A|-many witness functions (clause (b));
ℵ₀ pays for the ω-iteration of the closure. The bound does NOT silently absorb function
symbols into |A|: with the §3 record, fragments need not contain any atomic formulas, so
|Σ Functions| ≤ |A| is NOT available in general (see §10).

**Marker's Theorem 1.22 as a corollary.** When `|Σ n, L.Functions n| ≤ max ℵ₀ (mk A.toSet)`
(in particular: countable-symbol languages, or fragments containing an atomic mentioning each
function symbol), the bound collapses to `max(ℵ₀, |X|, |A|)` — and for infinite A, Marker's
`max(|A|, |X|)`.

**Countable corollary** (what #17 consumes): countable X, countable A.toSet, countable
Σ Functions ⇒ countable A-elementary substructure containing X.

## 7. Chain unions

**Primary theorem — common ambient, directed:** let (S_i)_{i ∈ I} be a directed family
(I directed, i ≤ j → S_i ≤ S_j) of substructures of ONE model M, each `AElementary A` in M and
with `S_i ≤ S_j` A-elementary as well (the pairwise condition follows from the two-in-M
conditions by the usual two-out-of-three lemma — state that lemma first). Then the directed
union `⨆ i, S_i` (Mathlib `Substructure` sSup / directed union, whose carrier is the union) is
`AElementary A` in M, and each `S_i` is A-elementary in the union.

- The induction: atomics free; `imp` components; `iInf`/`iSup` pointwise; `all` uses
  directedness — a tuple from the union lies in some single `S_i` (finitely many coordinates).
- **ω-chain corollary** and **ω₁-chain corollary** (continuity at limits stated explicitly:
  for a chain (S_α)_{α<ω₁} with S_λ = ⨆_{α<λ} S_α at limits, every S_α ≺_A ⋃ and the union is
  ≺_A M). This common-ambient form is what #16's iteration consumes; Marker's Ex 1.27
  (abstract chains of structures, no ambient) is DEFERRED — abstract direct limits only if a
  consumer demands them.

## 8. Finite-arity `OmitsType`

```
def OmitsType (M) (p : Set (L.BoundedFormulaω Empty n)) : Prop :=
  ∀ a : Fin n → M, ∃ φ ∈ p, ¬φ.Realize Empty.elim a
```

API for #16: omission passes DOWN to A-elementary substructures when `p ⊆ A`-members at arity
n (each tuple of N is a tuple of M; the failed formula transfers by truth agreement); omission
through chain unions (a union tuple lives in one link). No isolation theory here — that is the
existing `OmittingTypes.lean` machinery and #17's χ_p engine.

## 9. Reuse map

| Existing asset | Role here |
|---|---|
| `ModelTheory/LowenheimSkolem.lean` (`downward_LS`, `downward_LS_with_naming`, `L[[M]]` route) | UNCHANGED. Different theorem (countable model of a satisfiable sentence via Henkin/naming). The new LS is substructure-based; the two meet in #17 (companion model countable both ways). |
| `Language.withConstants` | Internal only, if the witness construction ever names parameters; the §5 choice-function route avoids it entirely. NOT in any public statement of #13. |
| `Methods/LocalSkolemUniversal.lean` (mixin) | Untouched; the EM-side Skolem interface. The audit confirms no shared code is needed — the fragment hull is semantic, the mixin is about `localColim` term structures. Cross-reference only. |
| `Admissible/Fragment/Core.lean` (`AdmissibleFragmentCore`) | Superseded-in-spirit: its `closed_iInf/closed_iSup` FORMATION fields are exactly what §3 forbids in the core. Per #18, the admissible interface will be rebuilt to EXTEND/WRAP this issue's `Fragment`; `AdmissibleFragmentCore` remains for the existing Barwise placeholder chain until #18 lands. No file is edited by #13. |
| `Lomega1omegaSmall`/`InfinitaryTypes` (#11) | Consumers (#17). The countable corollary of §6 plus type isolation gives the countable companion. |
| `Mathlib FirstOrder.Language.Substructure`, `Embedding`, closure `Substructure.closure` | The carrier layer for §5–§7: Mathlib's substructure closure already handles clause (a) (language functions); the hull adds the witness functions by an ω-iteration on carriers. |

## 10. Risk register and proposed declarations

**The key decision (atomic formulas).** Marker's Definition 1.18 (i)+(iii) jointly put EVERY
atomic formula (over arbitrary terms with variables in V) into every fragment, which forces
|A| ≥ |Σ Functions| whenever equality atomics exist — this is why his Theorem 1.22 can state
`max(|A|,|X|)`. The repository record (§3) does NOT require atomic membership: requiring it
would make countable fragments impossible over uncountable languages, breaking the
generated-countable-fragment results that #17 needs over arbitrary L (the same reason #11
needed the uniform collapse). Consequence: the honest LS bound carries `|Σ n, L.Functions n|`
explicitly (§6), and the textbook estimate is recovered as an explicit corollary, never
silently. This resolves the audit's controlling question: **textbook bound = specialization of
the honest repository theorem, with the absorption lemma stated, not assumed.**

Other risks:
- *Two-in-one-ambient vs pairwise chain hypotheses* (§7): the two-out-of-three lemma must come
  first or the corollaries will be stated with redundant hypotheses.
- *Embedding vs substructure phrasing of `AElementary`* (§4): embeddings are more general but
  every #13–#17 consumer uses substructure inclusions; state for embeddings only if it costs
  nothing in the first unit, else substructures with an embedding wrapper later.
- *`Fragment` countability*: keep as `(A.toSet).Countable` hypotheses (Set.Countable), not
  instances — mirrors `functionsIn_countable` style and avoids instance-resolution surprises
  on sigma-sets.
- *Generated fragment of a theory*: assumes the theory countable (sentence case automatic);
  the closure is the component-closure transitive hull, countable because each formula has
  countably many immediate components and the component relation is well-founded.

**Proposed Lean declarations** (implementation units 2–7, in order):

```
Fragment, Fragment.mem_* (unit 2: fragment API)
Fragment.generatedFrom (S : Set (Σ n, ...)), generatedFrom_countable,
  sentence/theory specializations (unit 3)
AElementary, refl/comp/transport, AElementary.theoryModel (unit 4)
Fragment.tarskiVaught_of_witnesses, the witness hull
  exists_aElementary_substructure (+ honest bound) (unit 5)
aElementary_iSup_of_directed (+ two-out-of-three, ω/ω₁ corollaries) (unit 6)
OmitsType, OmitsType.of_aElementary, OmitsType.iSup (unit 7)
```
