# Exercise 5.3 statement audit: the ℶ_{α+1} bounded-spectrum ladder

Date: 2026-07-11. Status: **audit complete; no Lean written**. Source: Marker, *Lectures on
Infinitary Model Theory*, lecture notes §5 (verbatim from the PDF, p. 56); cross-checked against
the Mathlib `Cardinal.beth` API. This document settles the five questions the ladder
implementation was gated on, and fixes the representation decisions.

## 0. Marker's verbatim statement

> **Exercise 5.3** Let α < ω₁. Let τ = {U_β : β ≤ α + 1} ∪ {E} ∪ {c₀, c₁, …} where U_β is a
> unary relation symbol, E is a binary relation symbol and c₀, c₁, … are constants. Let φ assert:
>
> i) U₀ = {c₀, c₁, …} and ∀x U_{α+1}(x);
> ii) U_γ ⊆ U_β for γ < β;
> iii) ∀x (U_β(x) ↔ ⋁_{β′<β} U_{β′}(x)) for β a limit ordinal;
> iv) ∀x∀y [(U_{β+1}(x) ∧ E(y, x)) → U_β(y)];
> v) if {x : E(x, y)} = {x : E(x, z)}, then y = z.
>
> a) Show that there is M ⊨ φ with |M| = ℶ_{α+1}.
> b) Show that every model of φ has cardinality at most ℶ_{α+1}.

Marker's beth recursion (p. 56): ℶ₀(κ) = κ and ℶ_α(κ) = sup_{β<α} 2^{ℶ_β(κ)}, with
ℶ_α := ℶ_α(ℵ₀). The section states: "The next exercise generalizes Exercise 1.26 and shows
that ℶ_{ω₁} is optimal."

## 1. The indexed language

- **Constants**: `Functions 0 := ℕ` (the `cₙ`), no other function symbols.
- **Relations**: one binary `E`, and unary level predicates indexed by the ordinals `β ≤ α+1`.
- **Type-0 obstruction and resolution**: `Ordinal` (and any subtype of it) lives in `Type 1`,
  but `Language.{0,0}` symbol types must be `Type 0`. **Decision**: index the levels by
  `(α + 2).toType` — the canonical `Type 0` well-order of order type `α + 2`, i.e. exactly
  `{β // β ≤ α + 1}` — with successor/limit structure read through the `Ordinal.typein`/`enum`
  API. This is the same `ToType` idiom the Marker machinery already uses for target orders.
- Concretely: `ladderLang (α) : Language.{0,0}` with `Functions 0 = ℕ`,
  `Relations 1 = (α + 2).toType`, `Relations 2 = Unit` (for `E`), all other arities empty.
- **Countability**: for `α < ω₁` both symbol sorts are countable (`ℕ`; and
  `(α + 2).toType` is countable since `α + 2 < ω₁`). So the sentence sits comfortably inside the
  countable-symbol world; no generated-sublanguage games are needed for the witnesses themselves.

## 2. Encoding the countable clause families — and the reusable helper

The clause families quantify over countable-but-not-`ℕ` index sets:
(ii) pairs `γ < β ≤ α+1`; (iii) one clause per limit `β ≤ α+1`, with an inner disjunction over
`{β′ // β′ < β}`; (iv) one clause per `β ≤ α`. The project's `iInf`/`iSup` are `ℕ`-indexed.

**Decision — build the reusable helper first** (independently useful for the fragment work #13
and everything after):

```
noncomputable def ciInf {ι : Type} [Countable ι] (φs : ι → L.BoundedFormulaω γ n) :
    L.BoundedFormulaω γ n
-- Nonempty ι: iInf (φs ∘ e) for a surjection e : ℕ → ι (from Countable + Nonempty);
-- empty ι: the tautology falsum.imp falsum.
theorem realize_ciInf : Realize (ciInf φs) v xs ↔ ∀ i, Realize (φs i) v xs
```

with the dual `ciSup` (empty default `falsum`) and `realize_ciSup ↔ ∃ i, …`. This is precisely
the `Theoryω.conjunction` pattern already landed, generalized from sentences over `Set` to
indexed families at any arity — the implementation transfers nearly verbatim.

The full sentence is then one `ciInf` over a clause datatype (or a `ℕ ⊕ pairs ⊕ …` sum):
- (i-a) `∀x (U₀ x → ciSup_n (x = cₙ))` and `ciInf_n (U₀ cₙ)`;
- (i-b) `∀x U_{α+1} x`;
- (ii) `ciInf` over `{(γ, β) // γ < β}` of `∀x (U_γ x → U_β x)`;
- (iii) `ciInf` over limit `β` of `∀x (U_β x → ciSup_{β′<β} U_{β′} x)` — the `←` direction is
  already (ii), so only `→` is needed (audit note: Marker writes `↔`; the reverse implication is
  subsumed, and dropping it simplifies both directions of the proof);
- (iv) `ciInf` over `β ≤ α` of `∀x∀y (U_{β+1} x → E y x → U_β y)`;
- (v) plain first-order extensionality: `∀y∀z ((∀x (E x y ↔ E x z)) → y = z)` — no infinitary
  quantification (as an ω-formula: two `imp`s through `equal`).

**Distinctness of the constants is NOT asserted and NOT needed**: the upper bound only uses
`U₀ ⊆ {cₙ-values}` (so `|U₀| ≤ ℵ₀`), and the lower bound exhibits a model where they happen to
be distinct. Omitting it also avoids any interaction between distinctness and extensionality at
the base (see §4).

## 3. The upper-bound induction (part b)

For `M ⊨ φ`, prove `|U_β^M| ≤ ℶ_β` by induction on `β ≤ α+1`:

- **Base**: `U₀ ⊆ {cₙ-values}` is a surjective `ℕ`-image, so `|U₀| ≤ ℵ₀ = ℶ₀`. (Same surjection
  argument as `CountableSpectrum.constInterp_surjective`, relativized to a predicate.)
- **Successor**: by (iv), for `y ∈ U_{β+1}` the `E`-predecessor set `pred(y) := {x : E x y}` is
  contained in `U_β`; by (v) — global extensionality — `y ↦ pred(y)` is injective on all of `M`,
  in particular on `U_{β+1}`, into `𝒫(U_β)`. So `|U_{β+1}| ≤ 2^{|U_β|} ≤ 2^{ℶ_β} = ℶ_{β+1}`.
- **Limit** `λ ≤ α+1`: by (iii→), `U_λ = ⋃_{β<λ} U_β` with `λ` countable, so
  `|U_λ| ≤ ℵ₀ ⊗ sup_{β<λ} |U_β| ≤ ℵ₀ ⊗ sup_{β<λ} ℶ_β = ℶ_λ` (the sup is `ℶ_λ ≥ ℵ₀`; countable
  unions need `Cardinal.mk_iUnion_le`-style lemmas plus `aleph0 ⊗ κ = κ` for infinite `κ`).
- **Conclusion**: by (i-b) the universe is `U_{α+1}`, so `|M| ≤ ℶ_{α+1}`.

**Cardinal-only prerequisites to prove first** (the "cardinal ladder lemmas" — no syntax):
1. injective-into-powerset bound: `Function.Injective (f : X → Set Y) → mk X ≤ 2 ^ mk Y`
   (essentially `Cardinal.mk_le_of_injective` + `mk (Set Y) = 2 ^ mk Y` = `Cardinal.mk_set`);
2. countable-union bound: a union over a countable index of sets each of size `≤ κ` (κ infinite)
   has size `≤ κ`;
3. the indexing agreement: Mathlib's `Cardinal.beth` (`beth 0 = ℵ₀`, `beth (succ) = 2 ^ beth`,
   `beth limit = ⨆`) agrees with Marker's `ℶ_α = sup_{β<α} 2^{ℶ_β}` for all `α` — a two-line
   induction, worth stating once so the ladder never touches the raw recursion again.

## 4. The maximal-model representation (part a)

**The key design question.** Type-level transfinite recursion (`X_{β+1} = X_β ⊕ Set X_β` with
identifications) needs colimits/quotients and breaks extensionality across levels — rejected.

**Decision, α = 0 (the powerset witness — fully `Type 0`, no recursion):**
carrier `Set ℕ` with

- `cₙ ↦ ({n} : Set ℕ)`, `U₀ := {s | ∃ n, s = {n}}` (the singletons), `U₁ := univ`;
- `E x y :↔ ∃ n, x = {n} ∧ n ∈ y`.

Checks: (i) `U₀` is exactly the constants ✓; (ii) trivial; (iii) vacuous (no limit `β ≤ 1`);
(iv) every `E`-predecessor is a singleton ✓; (v) `pred(y) = {{n} : n ∈ y}` determines `y`
(injective for ALL `y : Set ℕ`, including `pred(s) = ∅ ↔ s = ∅`) ✓; and
`mk (Set ℕ) = 2 ^ ℵ₀ = ℶ_1` ✓. Through `lt_Lomega1omegaHanfNumber_of_maximal_model` this yields
**`beth_one_lt_Lomega1omegaHanfNumber`** with `hmodel := ⟨Set ℕ, …⟩` and `hupper` from §3
(instantiated at `α = 0`, or proved directly for the single-step bound).

**Decision, general α — SET-level recursion inside `ZFSet`, then shrink:**

- `Y : Ordinal → ZFSet` by `Ordinal.limitRecOn`: `Y 0 := ZFSet.omega` (or the singletons-image
  of it), `Y (β+1) := Y β ∪ ZFSet.powerset (Y β)`, `Y λ := ⋃ β<λ, Y β` (set-level unions — no
  type colimits). Carrier `{x : ZFSet // x ∈ Y (α+1)}`, `U_β := (· ∈ Y β)`, `E := (∈)`.
  Global extensionality (v) is ZF-extensionality — free. Cumulativity gives (ii)/(iii); rank
  discipline gives (iv); base coding gives (i).
- **Base subtlety**: with `E = ∈` and von Neumann naturals, `pred(n) = {0,…,n−1} ⊆ Y 0` — fine
  for (iv) (it only constrains `U_{β+1}`-elements downward, and base predecessors land in the
  base). Extensionality is global ZF-extensionality, so no collapse issue. Alternatively code
  the base as singletons `{n}` exactly as in the α = 0 model; decide at implementation time by
  whichever makes (i)'s "`U₀` = constants" cleanest.
- **Universe obstruction**: `ZFSet : Type 1`, but `IsHanfBound` quantifies over `M : Type 0`.
  The carrier has `mk ≤ lift ℶ_{α+1}`, hence is `Small.{0}`; transport the structure across
  `Shrink`. This is the main friction point of the general ladder — an isolated, mechanical
  step, but it needs the `ZFSet`-cardinality bridge:
  `mk {y // y ∈ ZFSet.powerset x} = 2 ^ mk {y // y ∈ x}` (injectivity from extensionality;
  surjectivity from `ZFSet.sep` comprehension with a classical predicate) and
  `mk {y // y ∈ ZFSet.omega} = ℵ₀`. **These two lemmas are the audit's identified risk**: if
  Mathlib's `ZFSet` API makes them painful, the fallback is the reviewer's contingency — stop
  the ladder at `ℶ_1 < H` (already valuable) and switch to #13/#8.
- **Finite α** needs no `ZFSet`: iterate the α = 0 pattern with carrier `Set^k ℕ`? — NO: the
  cumulative union across levels re-raises the identification problem in types. Finite stages
  should also use the `ZFSet` route (where they are trivial instances), or be skipped in favor
  of going directly from α = 0 to the general construction. **Decision: skip bespoke finite
  stages; do α = 0 concretely, then the general `ZFSet` ladder.** (Revises the earlier
  "finite stages next" ordering: the audit shows finite stages share ALL the general case's
  difficulties except limit clauses, so they are not a meaningful de-risking step.)

## 5. The endpoint supremum

Each stage α gives, via the generic endpoint, `ℶ_{α+1} < Lomega1omegaHanfNumber` — in
particular `ℶ_{α+1} ≤ H` for every `α < ω₁`. Then:

- `sup_{α<ω₁} ℶ_{α+1} = ℶ_{ω₁}`: `ω₁` is a limit, `Cardinal.beth` is continuous at limits
  (`beth_limit : beth o = ⨆ a : Iio o, beth a`), and `α ↦ α+1` is cofinal in `ω₁`. One lemma:
  `⨆ (α : Iio (ω₁ : Ordinal)), beth (α + 1) = beth ω₁` (both `≤` directions from monotonicity
  + cofinality).
- Hence `ℶ_{ω₁} ≤ Lomega1omegaHanfNumber`; with the released
  `Lomega1omegaHanfNumber_le_beth_omega1` this closes **`Lomega1omegaHanfNumber = ℶ_{ω₁}`** —
  the sharpness theorem.
- Indexing check passed: no off-by-one — stage α is a sentence in `ladderLang α` (levels up to
  `α+1`) with spectrum bounded by (and attaining) `ℶ_{α+1}`; the `+1`s in Marker's statement and
  Mathlib's `beth` line up without adjustment.

## Implementation plan (in commit order)

1. `ciInf`/`ciSup` over countable index types + realize lemmas (`Lomega1omega/Operations`-level,
   reusable; models `Theoryω.conjunction`).
2. Cardinal ladder lemmas (§3 items 1–3, plus §5's supremum lemma) — no syntax.
3. `HanfSpectrum/Powerset.lean`: the α = 0 model on `Set ℕ` and
   `beth_one_lt_Lomega1omegaHanfNumber` (can use a hand-rolled 2-level sentence OR the general
   `ladderLang` instantiated; prefer `ladderLang` if item 4 is imminent, hand-rolled if the
   spike takes priority).
4. `ZFSet` cardinality bridge (the risk item — timebox it; on failure invoke the contingency).
5. `HanfSpectrum/BethLadder.lean`: `ladderLang α`, the sentence, the `ZFSet` maximal model +
   `Shrink`, the upper-bound induction, the per-stage witness, the supremum, and
   `Lomega1omegaHanfNumber_eq_beth_omega1`.

## Bonus capture (for #12)

Page 54 of the same PDF has the exact statement this audit's fetch surfaced: **Corollary 4.34**
— τ countable with binary `<`, `M ⊨ φ` with `<` of order type ω₁, then there is `N ⊨ φ` of
cardinality ℵ₁ with an order-preserving embedding of (ℚ, <) — proved from Theorem 4.30
(A-elementary end extensions via omitting types) + Corollary 4.31 (ℵ₁-chains) + Theorem 4.26.
So #12's actual dependency chain in Marker runs through **end extensions and elementary chains**
(i.e., issue #13 material), not just the bare consistency property; #12 should be updated when
work starts on it.
