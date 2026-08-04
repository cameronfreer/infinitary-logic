# Carrier-parameterized syntax spike — findings at the stop checkpoint

Branch `api/fixed-index-infinitary-syntax`, file `spike/CarrierSyntax.lean` (outside the module
tree; `lake env lean spike/CarrierSyntax.lean`). All gates pass: 0 sorries, exit 0, headline
declarations axiom-clean (`propext`, `Classical.choice`, `Quot.sound`; `reindex_comp` needs no
choice). Local and unposted: no Zulip, no Mathlib-branch changes, no PR.

## 1. The verdict

Aaron Liu's design survives every falsification gate, including the two that motivated the
current architecture:

- **Universes.** `BoundedFormulaIdx L ι α n : Type (max u v uα uι)` — the `uι + 1` bump of the
  current `BoundedFormulaInf` is gone, and `BoundedFormulaOmega := BoundedFormulaIdx ℕ` lands at
  `Type (max u v uα)`, *exactly* the current `BoundedFormulaω` universe. Lω₁ω is a definitional
  specialization, not a second inductive.
- **Karp.** The backward direction needs an `N`-indexed and an `M`-indexed conjunction over one
  formula type; the single carrier `M ⊕ N` supports both through the canonical sum codings. No
  constructor-quantified index types, no universe lifts anywhere in the statement or proof.
- **Rank (the flagged main risk).** `qrank : BoundedFormulaIdx ι α n → Ordinal.{uι}` typechecks,
  lands in `Ordinal.{0}` at the ℕ carrier, and transports along `reindex` up to `Ordinal.lift`,
  including over empty carriers.

## 2. Proposed production API

```lean
inductive BoundedFormulaIdx (L : Language.{u, v}) (ι : Type uι) (α : Type uα) :
    ℕ → Type (max u v uα uι)
  -- falsum | equal | rel | imp | all | iSup (φs : ι → …) | iInf (φs : ι → …)

abbrev BoundedFormulaOmega L α n := L.BoundedFormulaIdx ℕ α n   -- Lω₁ω, definitionally

-- Codings between carriers: the reusable transport layer
structure IndexCoding (ι : Type uι) (κ : Type uκ) where
  encode : ι → κ
  decode : κ → Option ι
  decode_encode : ∀ i, decode (encode i) = some i
-- id, comp, sumInl, sumInr, ofEncodable (Encodable, no choice); pad (⊤/⊥-neutral extension)

-- ι-indexed connectives at carrier κ, along a coding (padding is semantically neutral):
def codediInf (c : IndexCoding ι κ) (φs : ι → L.BoundedFormulaIdx κ α n) : L.BoundedFormulaIdx κ α n
def codediSup …    -- realize_codediInf / realize_codediSup: generic, one equation each

-- Whole-formula transport (replaces liftUI and the embedding triangle):
def reindex (c : IndexCoding ι κ) : L.BoundedFormulaIdx ι α n → L.BoundedFormulaIdx κ α n
theorem realize_reindex   -- semantic preservation (hence equivalence transport, both ways)
theorem reindex_id        -- syntactic identity law
theorem reindex_comp      -- syntactic composition law (no choice axiom)

def toOmega [Encodable ι] : L.BoundedFormulaIdx ι α n → L.BoundedFormulaOmega α n
  -- := reindex (.ofEncodable ι); Countable corollary via choice OUTSIDE the operation

noncomputable def qrank : L.BoundedFormulaIdx ι α n → Ordinal.{uι}
theorem qrank_reindex (c : IndexCoding ι κ) :
    Ordinal.lift.{uι} (reindex c φ).qrank = Ordinal.lift.{uκ} φ.qrank
```

Equivalence layering — the universal quantifier over index types lives **outside** the syntax:

```lean
def InfEquivAt (L) (ι : Type uι) (M N : Type w) : Prop := ∀ φ : L.SentenceIdx ι, φ.Realize M ↔ φ.Realize N
def InfEquivW  (L) (M N : Type w) : Prop := ∀ ι : Type w, InfEquivAt L ι M N
```

## 3. Exact Karp packaging (proved against the REAL `PotentialIso`)

The spike imports `InfinitaryLogic.Karp.PotentialIso` — the production back-and-forth notion,
which is syntax-independent — so the left-hand side below is literally the production one.

```lean
theorem PotentialIso.infEquivAt (P : PotentialIso L M N) (ι : Type uι) : InfEquivAt L ι M N
  -- forward: generic in the carrier AND its universe

theorem infEquivAt_sum_implies_potentialIso :
    InfEquivAt L (M ⊕ N) M N → Nonempty (PotentialIso L M N)
  -- backward: the ONE carrier M ⊕ N suffices; conjunctions are codediInf at sumInl/sumInr

theorem karp_theorem_on_sum : Nonempty (PotentialIso L M N) ↔ InfEquivAt L (M ⊕ N) M N
theorem karp_theorem_idx    : Nonempty (PotentialIso L M N) ↔ InfEquivW L M N   -- pure packaging
```

A structural bonus found during the port: stating the back-and-forth family over formulas with
`Empty` free variables and `p.1` **bound** variables (tuple in bound positions) lets `existsLast`
do all quantification. The production proof's `existsLastVarInf` + `insertLastBoundInf` +
`relabel` support (~150 lines of `Fin` plumbing in `Linf/Operations.lean`) and the
`Fin.append`/`finSumFinEquiv` gymnastics in `Karp/Theorem.lean`'s induction are **not needed** in
this formulation. The spike's forward induction `all` case consumes `forth`/`back` directly.

## 4. Which current declarations this supersedes (L1/L2 of the Mathlib plan)

| Current | Replacement | Note |
|---|---|---|
| `BoundedFormulaω` + `BoundedFormulaInf` parallel inductives | one `BoundedFormulaIdx` + `abbrev` | universe-exact at `ι := ℕ` |
| L1: `realize_iSup/iInf` pinned at `{ι : Type}` (`Linf/Semantics.lean:77,81`) | one generic equation per connective, `Iff.rfl` | the L1 tranche disappears |
| `liftUI` (source universe 0 only, `Linf/Operations.lean:190`) | `reindex` along a coding | honest universes on both sides |
| `toLω_toLinf` triangle (nonexistent; L2's goal) | `reindex_comp` | syntactic, choice-free |
| `realize_liftUI` | `realize_reindex` | |
| `einf`/`esup` Encodable adapters | `codediInf`/`codediSup` at `ofEncodable`, `toOmega` | choice only in the `Countable` corollary |
| `LinfEquivW` (index types inside the syntax at `uι = w`) | `InfEquivW := ∀ ι : Type w, InfEquivAt ι` | quantifier moved outside the syntax |
| `karp_theorem_w` | `karp_theorem_idx` (via `karp_theorem_on_sum`) | same `PotentialIso` LHS |
| `existsLastVarInf` + `insertLastBoundInf` + support lemmas | bound-variable family + `existsLast` | *for the Karp proof*; a general free-var quantifier may still be wanted by other consumers |
| L1-deferred qrank universe audit | `qrank : Ordinal.{uι}` + `qrank_reindex` | the audit's question is answered |

## 5. Remaining obstacles / not yet spiked

- **Rank transport is NOT an obstacle** — proved. One Mathlib gap surfaced: `Ordinal.lift_iSup`
  does not exist (the `Cardinal` version does); the spike hand-proves `lift_iSup_ord` via
  `mem_range_lift_of_le`. Candidate small upstream lemma.
- **Mixed-carrier formulas — audit COMPLETE (PR #43 comment).** The old `BoundedFormulaInf`
  lets *each node* pick its own index type; the new syntax fixes one carrier per formula. The
  sweep of every node-construction site found exactly ONE genuine mixed-carrier construction in
  the tree: the old Karp backward proof itself, i.e. precisely the site the spike re-founded at
  `M ⊕ N`. No current production consumer requires a `Σ`-type escape hatch.
- **Operations layer unspiked**: `mapTermRel`/`relabel`/`subst`/`mapFreeVars` for the new type
  (mechanical — one extra `ι`-family case each, no new universe content expected).
- **Fragments unspiked — and formula-level countability stays formula-sensitive.** A fixed
  carrier does not mean every formula contains an infinitary node: a finitary formula at an
  uncountable carrier is still countable. So `indexBound` becomes simpler but not global — its
  only possible infinitary contribution is `Cardinal.mk ι`, giving `0` for formulas with no
  infinitary node and `Cardinal.mk ι` once one occurs — and `IsCountable`/`IsKappa` cannot be
  replaced by carrier constraints alone. `toOmega` covers the uniform `[Encodable ι]` case; the
  proof-directed `ofCountable` still needs a compatibility wrapper that recurses structurally,
  obtaining `Countable ι` only when it actually reaches an infinitary node. When that layer is
  ported, add a regression: `toInf` at an arbitrary (possibly uncountable) carrier is
  `IsCountable` and converts to `BoundedFormulaω`. Scott's `FormulaCode` counting route also
  needs a look.
- **Deprecations to carry into any production port**: `push_neg` → `push Not`;
  `Ordinal.bddAbove_range` → `Ordinal.bddAbove_of_small` / `Ordinal.le_iSup` (+ `small_max`,
  which is deliberately not an instance — lean4#2297).
- **Placement open question** for a Mathlib PR: where `IndexCoding` lives (it is
  logic-independent; arguably `Logic/Encodable` territory rather than `ModelTheory`).

## 6. Induction gotcha (worth keeping)

`induction φ` on a formula whose arity is a *literal* (e.g. `0`) fails with "Index in target's
type is not a variable" — this looks exactly like the `abbrev` specialization breaking the
recursor, but is just the fixed index; state at general arity and it works.
