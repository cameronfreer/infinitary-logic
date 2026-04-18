/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.Hanf
import InfinitaryLogic.Methods.EM.FragmentAdapter
import InfinitaryLogic.Methods.EM.Extraction

/-!
# Morley-Hanf Transfer Hypothesis (Conditional)

This file isolates the deep combinatorial transfer hypothesis needed for the
Morley-Hanf theorem. The hypothesis encapsulates Erdős-Rado extraction +
Ehrenfeucht-Mostowski stretching, which require infrastructure not currently
formalized in Lean or Mathlib.

## Conditional Status

`MorleyHanfTransfer` is a `Prop`-valued definition, not a theorem. The
conditional theorem `morley_hanf_of_transfer` takes it as a hypothesis.
Both are placed in `Conditional/` to make the external dependency visible.

## References

- [Mar16], §5
- [KK04], §1.6
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure

/-- **Deep set-theoretic/model-theoretic transfer hypothesis** for the Morley-Hanf theorem.

This encapsulates the combined content of:
1. **Erdős-Rado extraction**: Models of size ≥ ℶ_{ω₁} in a countable language
   contain Lω₁ω-indiscernible sequences of uncountable length.
2. **Ehrenfeucht-Mostowski stretching**: Such indiscernible sequences can be
   stretched to produce models of arbitrary size satisfying the same Lω₁ω sentences.

These deep combinatorial arguments (Ramsey/partition calculus + EM functors)
require infrastructure not currently formalized in Lean or Mathlib.

See [Mar16], §5; [KK04], §1.6. -/
def MorleyHanfTransfer (L : Language.{u, v}) [Countable (Σ l, L.Relations l)] : Prop :=
  ∀ (φ : L.Sentenceω) (M : Type) [L.Structure M],
    Sentenceω.Realize φ M → Cardinal.mk M ≥ Cardinal.beth (Ordinal.omega 1) →
    HasArbLargeModels φ

/-- **Morley-Hanf Theorem** (conditional on transfer hypothesis).

For a countable language, the Hanf number of any Lω₁ω sentence is bounded
by ℶ_ω₁ (the ω₁-th beth number), assuming the deep combinatorial transfer
principle `MorleyHanfTransfer`.

The unconditional version requires formalizing Erdős-Rado partition calculus
and Ehrenfeucht-Mostowski functors for Lω₁ω, which are not currently available
in Lean or Mathlib.

**Boundary**: The hypothesis `htransfer` captures exactly the deep
set-theoretic/model-theoretic transfer step. All other reasoning is formalized. -/
@[blueprint "thm:morley-hanf"
  (title := /-- Morley-Hanf bound -/)
  (statement := /-- Conditional on the Morley-Hanf transfer hypothesis,
    $\beth_{\omegaone}$ is a Hanf bound for every $\Lomegaone$ sentence. -/)
  (proof := /-- Given a model of size $\geq \beth_{\omegaone}$, the transfer
    hypothesis directly yields arbitrarily large models. -/)
  (uses := ["def:hanf-bound", "def:arb-large-models"])]
theorem morley_hanf_of_transfer [Countable (Σ l, L.Relations l)]
    (htransfer : MorleyHanfTransfer L) (φ : L.Sentenceω) :
    IsHanfBound φ (Cardinal.beth (Ordinal.omega 1)) := by
  intro ⟨M, hStr, hφ, hsize⟩
  exact htransfer φ M hφ hsize

/-! ### Residual extraction hypothesis + proved bridge

Phase 2 refactor: split `MorleyHanfTransfer` into a source-side extraction
hypothesis (still conditional) plus a compactness oracle, joined by a proved
bridge theorem. The extraction is the genuine combinatorial residual
(Erdős–Rado + pairwise-distinct stable-type extraction); the stretching
side is now fully formalized in `Methods/EM/FragmentAdapter.lean`.

Universe note: the bridge uses `L : Language.{0, 0}` so that the target
linear order `J : Type` (produced via `(Cardinal.ord κ).ToType` at
`Cardinal.{0}`) matches the universe expected by the stretching theorems
(which take `{J : Type u}` tied to `L`'s first universe). -/

section RestrictedBridge

variable {L' : Language.{0, 0}} [Countable (Σ l, L'.Relations l)]

/-- **Residual source-side extraction hypothesis.**

From a model of size ≥ ℶ_ω₁ in a countable-relational language, extract a
pairwise-distinct `ℕ`-indexed sequence that is restricted-indiscernible
on any chosen countable formula family `s`.

This is the genuine combinatorial content left after separating out EM
stretching: Erdős–Rado-style partition arguments for Lω₁ω plus a stable-type
extraction. The sequence does NOT need to have an uncountable index set —
Phase 1's arbitrary-J stretching means a countable source suffices. -/
def MorleyHanfExtraction : Prop :=
  ∀ (s : ℕ → Σ n, L'.BoundedFormulaω Empty n) (M : Type) [L'.Structure M],
    Cardinal.mk M ≥ Cardinal.beth (Ordinal.omega 1) →
    ∃ (a : ℕ → M),
      (∀ i j : ℕ, i ≠ j → a i ≠ a j) ∧
      IsLomega1omegaIndiscernibleOn a (Set.range s)

omit [Countable (Σ l, L'.Relations l)] in
/-- **Morley–Hanf via restricted extraction + compactness** (proved).

Assuming the residual extraction hypothesis `MorleyHanfExtraction L` and a
per-target compactness oracle for every `L[[J]]`, any sentence realized in a
model of size ≥ ℶ_ω₁ has arbitrarily large models.

The proof combines:
  - `hExtract` to obtain a pairwise-distinct ℕ-indexed sequence that is
    restricted-indiscernible on `{⟨0, φ⟩, ⟨2, disEqFormula⟩}`,
  - `stretch_restricted_sequence_of_compact` (tranche 2b) to stretch
    the sequence into a target model `N` over an arbitrarily large `J`,
  - inline derivations of (a) sentence preservation from the empty-tuple
    application of the stretching equivalence, and (b) injectivity of
    `b : J → N` from the pair-tuple application. -/
@[blueprint "thm:morley-hanf-restricted"
  (title := /-- Morley-Hanf via restricted extraction -/)
  (statement := /-- Assuming restricted source-side extraction and a per-target
    compactness oracle, every Lω₁ω sentence satisfied in a model of size
    $\geq \beth_{\omegaone}$ has arbitrarily large models. -/)
  (proof := /-- Extract a pairwise-distinct ℕ-indexed sequence
    restricted-indiscernible on the family $\{\varphi, x_0 \neq x_1\}$, stretch
    along an ordinal of the target cardinality, and read off $\varphi$
    preservation and injectivity from the sequence-form equivalence. -/)
  (uses := ["def:arb-large-models"])]
theorem hasArbLargeModels_of_restricted_extraction
    (hExtract : MorleyHanfExtraction (L' := L'))
    (hCompact : ∀ (J : Type) [LinearOrder J] (S : Set L'[[J]].Sentenceω),
      (∀ F : Set L'[[J]].Sentenceω, F.Finite → F ⊆ S →
        ∃ (N : Type) (_ : L'[[J]].Structure N), Theoryω.Model F N) →
      ∃ (N : Type) (_ : L'[[J]].Structure N), Theoryω.Model S N)
    (φ : L'.Sentenceω)
    (hφ : ∃ (M : Type) (_ : L'.Structure M), Sentenceω.Realize φ M ∧
      Cardinal.mk M ≥ Cardinal.beth (Ordinal.omega 1)) :
    HasArbLargeModels φ := by
  classical
  obtain ⟨M, instM, hRealizeM, hSizeM⟩ := hφ
  -- Formula family: s 0 = ⟨0, φ⟩, s 1 = ⟨2, disEqFormula⟩, rest pad with ⟨0, φ⟩.
  let s : ℕ → Σ n, L'.BoundedFormulaω Empty n := fun i =>
    match i with
    | 0 => ⟨0, φ⟩
    | 1 => ⟨2, disEqFormula⟩
    | _ + 2 => ⟨0, φ⟩
  have hs0 : s 0 = ⟨0, φ⟩ := rfl
  have hs1 : s 1 = ⟨2, disEqFormula⟩ := rfl
  have h_range_φ : ⟨0, φ⟩ ∈ Set.range s := ⟨0, rfl⟩
  have h_range_dis : ⟨(2 : ℕ), (disEqFormula : L'.BoundedFormulaω Empty 2)⟩ ∈
      Set.range s := ⟨1, rfl⟩
  -- Extract pairwise-distinct + restricted-indiscernible a : ℕ → M.
  obtain ⟨a, hPairwise, hIndisc⟩ := hExtract s M hSizeM
  -- HasArbLargeModels target: ∀ κ, ∃ N of size ≥ κ realizing φ.
  intro κ
  -- Target linear order J of cardinality κ.
  let J : Type := (Cardinal.ord κ).ToType
  haveI : LinearOrder J := linearOrder_toType _
  have hJ_card : Cardinal.mk J = κ := Cardinal.mk_ord_toType κ
  -- Apply the compact-oracle sequence stretching.
  obtain ⟨N, instN, b, hSeq⟩ :=
    IsLomega1omegaIndiscernibleOn.stretch_restricted_sequence_of_compact (J := J) s hIndisc
      (Order.succ (Ordinal.omega0 : Ordinal.{0}))
      (Order.lt_succ (Ordinal.omega0 : Ordinal.{0})) (hCompact J)
  letI : L'.Structure N := (L'.lhomWithConstants J).reduct N
  refine ⟨N, inferInstance, ?_, ?_⟩
  · -- Sentence preservation: φ is realized in N.
    -- Apply hSeq at i = 0 with the unique empty embedding Fin 0 ↪o J.
    have hSeq_at_0 := hSeq 0
    rw [hs0] at hSeq_at_0
    dsimp only at hSeq_at_0
    let t0 : Fin 0 ↪o J :=
      ⟨⟨Fin.elim0, fun ⟨_, hk⟩ => absurd hk (Nat.not_lt_zero _)⟩, fun {x} => x.elim0⟩
    have hkey := hSeq_at_0 t0
    have hbt0 : (b ∘ t0 : Fin 0 → N) = Fin.elim0 := funext fun k => k.elim0
    rw [hbt0] at hkey
    -- Template truth of φ at `templateOfSeq a`: ∃ u : Fin 0 → ℕ, StrictMono u ∧ ...
    -- The unique u is Fin.elim0, and a ∘ Fin.elim0 = Fin.elim0, giving
    -- φ.Realize Empty.elim Fin.elim0 = Sentenceω.Realize φ M, true by hRealizeM.
    have hTmpl : (templateOfSeq a : Lomega1omegaTemplate L').truth φ := by
      refine ⟨Fin.elim0, ?_, ?_⟩
      · intro ⟨_, hk⟩ _ _; exact absurd hk (Nat.not_lt_zero _)
      · have : (a ∘ Fin.elim0 : Fin 0 → M) = Fin.elim0 := funext fun k => k.elim0
        rw [this]; exact hRealizeM
    show Sentenceω.Realize φ N
    exact hkey.mpr hTmpl
  · -- Injectivity ⇒ #N ≥ #J = κ.
    -- Template truth of disEqFormula: witnessed by strictMono u = ![0, 1] in ℕ
    -- with a 0 ≠ a 1 from pairwise-distinctness.
    have hDisTruth : (templateOfSeq a : Lomega1omegaTemplate L').truth disEqFormula := by
      refine ⟨![0, 1], ?_, ?_⟩
      · intro p q hpq
        match p, q, hpq with
        | ⟨0, _⟩, ⟨1, _⟩, _ => exact Nat.zero_lt_one
        | ⟨0, _⟩, ⟨0, _⟩, h => exact absurd h (lt_irrefl _)
        | ⟨1, _⟩, ⟨1, _⟩, h => exact absurd h (lt_irrefl _)
        | ⟨1, _⟩, ⟨0, _⟩, h =>
          have hval : (1 : ℕ) < 0 := h
          exact absurd hval (by omega)
      · simp only [disEqFormula, BoundedFormulaω.realize_not, BoundedFormulaω.realize_equal,
          Term.realize_var]
        have h01 : (0 : ℕ) ≠ 1 := by decide
        exact fun heq => hPairwise 0 1 h01 (by simpa using heq)
    have hSeq_at_1 := hSeq 1
    rw [hs1] at hSeq_at_1
    dsimp only at hSeq_at_1
    -- helper: from b j₀ = b j₁ with j₀ < j₁, derive contradiction.
    have hbInj : Function.Injective b := by
      have helper : ∀ {j₀ j₁ : J}, j₀ < j₁ → b j₀ = b j₁ → False := by
        intro j₀ j₁ hlt heq
        have hmono : StrictMono (![j₀, j₁] : Fin 2 → J) := by
          intro p q hpq
          match p, q, hpq with
          | ⟨0, _⟩, ⟨1, _⟩, _ => exact hlt
          | ⟨0, _⟩, ⟨0, _⟩, h => exact absurd h (lt_irrefl _)
          | ⟨1, _⟩, ⟨1, _⟩, h => exact absurd h (lt_irrefl _)
          | ⟨1, _⟩, ⟨0, _⟩, h =>
            have hval : (1 : ℕ) < 0 := h
            exact absurd hval (by omega)
        set t : Fin 2 ↪o J := OrderEmbedding.ofStrictMono ![j₀, j₁] hmono with ht_def
        have hrealize := (hSeq_at_1 t).mpr hDisTruth
        simp only [disEqFormula, BoundedFormulaω.realize_not, BoundedFormulaω.realize_equal,
          Term.realize_var] at hrealize
        apply hrealize
        show b (t 0) = b (t 1)
        have h0 : t 0 = j₀ := by simp [ht_def, OrderEmbedding.coe_ofStrictMono]
        have h1 : t 1 = j₁ := by simp [ht_def, OrderEmbedding.coe_ofStrictMono]
        rw [h0, h1]; exact heq
      intro j j' hbjj'
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact helper hlt hbjj'
      · exact helper hlt hbjj'.symm
    -- #N ≥ #J = κ via injection.
    calc Cardinal.mk N ≥ Cardinal.mk J := Cardinal.mk_le_of_injective hbInj
      _ = κ := hJ_card

/-! ### Combinatorial residual via `IsIndiscernibleOnSet` -/

/-- **Combinatorial residual** (model-theoretic form): from a model of
size ≥ ℶ_ω₁ under some chosen linear order on its carrier, produce an
infinite strictly-monotone `ℕ → M` sequence whose range is
`IsIndiscernibleOnSet` for the countable formula family `s`.

This is the Erdős–Rado content of `MorleyHanfExtraction` isolated from
the model-theoretic plumbing: no reference to `IsLomega1omegaIndiscernibleOn`,
no pairwise-distinct clause — only the combinatorial statement
"large model + countable formula family ⇒ infinite homogeneous ω-sequence."

The hypothesis still quantifies over `L`, `M`, and formulas. The truly
pure partition-calculus form is `PureColoringHypothesis` (below), which
implies this via `indiscernibleSequence_of_pureColoring`. -/
def IndiscernibleSequenceHypothesis : Prop :=
  ∀ (s : ℕ → Σ n, L'.BoundedFormulaω Empty n)
    (M : Type) [L'.Structure M] (_ : LinearOrder M),
    Cardinal.mk M ≥ Cardinal.beth (Ordinal.omega 1) →
    ∃ (f : ℕ → M), StrictMono f ∧
      IsIndiscernibleOnSet (id : M → M) (Set.range s) (Set.range f)

omit [Countable (Σ l, L'.Relations l)] in
/-- **Reduction**: the combinatorial residual
`IndiscernibleSequenceHypothesis` implies `MorleyHanfExtraction`.

Given the hypothesis plus `|M| ≥ ℶ_ω₁`, equip `M` with a classical
linear order (via `WellOrderingRel` / `Classical.choice`), apply the
hypothesis to obtain a strict-monotone `f : ℕ → M` whose range is
`IsIndiscernibleOnSet` for `Set.range s`. Strict-monotonicity gives
pairwise distinctness (injectivity), and the sequence-level reduction
`IsIndiscernibleOnSet.toLomega1omegaIndiscernibleOn` (Phase 2d0a) gives
the restricted indiscernibility. -/
theorem morleyHanfExtraction_of_indiscernibleSequence
    (hSeq : IndiscernibleSequenceHypothesis (L' := L')) :
    MorleyHanfExtraction (L' := L') := by
  intro s M _ hSize
  -- Equip `M` with a classical linear order via its `LinearOrder` instance
  -- given by the classical well-ordering of its cardinality.
  letI : LinearOrder M := Classical.choice (by
    have : Nonempty (LinearOrder M) := ⟨IsWellOrder.linearOrder WellOrderingRel⟩
    exact this)
  obtain ⟨f, hfMono, hfInd⟩ := hSeq s M ‹LinearOrder M› hSize
  refine ⟨f, ?_, ?_⟩
  · -- Pairwise distinct: strict-mono → injective.
    intro i j hij
    exact hfMono.injective.ne hij
  · -- Restricted indiscernibility: apply the 2d0a reduction.
    intro n φ hmem u v hu hv
    -- From 2d0a: range f is indiscernible, so truth agrees on `f ∘ u` and `f ∘ v`.
    have hfu : StrictMono (f ∘ u) := hfMono.comp hu
    have hfv : StrictMono (f ∘ v) := hfMono.comp hv
    have huR : ∀ k, (f ∘ u) k ∈ Set.range f := fun k => ⟨u k, rfl⟩
    have hvR : ∀ k, (f ∘ v) k ∈ Set.range f := fun k => ⟨v k, rfl⟩
    exact hfInd hmem (f ∘ u) (f ∘ v) hfu hfv huR hvR

end RestrictedBridge

/-! ### Pure partition-calculus residual -/

/-- **Pure partition-calculus residual**: for every linearly-ordered type
`I` with `|I| ≥ ℶ_ω₁` and every countable family of Bool-valued colorings
on finite-arity increasing tuples (order-embeddings) from `I`, there
exists an infinite strictly-monotone `ℕ → I` sequence whose range is
monochromatic for every coloring in the family.

The body mentions no language, no structure, no formula — only a linear
order, cardinalities, `ℕ`-indexed arities, and `Bool` colorings on
`Fin n ↪o I`. This is the Erdős–Rado statement proper; Phase 2d targets
it directly. `indiscernibleSequence_of_pureColoring` below proves that
this implies the larger `IndiscernibleSequenceHypothesis`. -/
def PureColoringHypothesis : Prop :=
  ∀ (I : Type) [LinearOrder I],
    Cardinal.mk I ≥ Cardinal.beth (Ordinal.omega 1) →
    ∀ (c : ℕ → Σ n, (Fin n ↪o I) → Bool),
    ∃ (f : ℕ → I), StrictMono f ∧
      ∀ (i : ℕ) (t t' : Fin (c i).1 ↪o I),
        (∀ k, t k ∈ Set.range f) → (∀ k, t' k ∈ Set.range f) →
        (c i).2 t = (c i).2 t'

/-- **Reduction**: the pure partition-calculus hypothesis implies the
model-theoretic `IndiscernibleSequenceHypothesis`. The colorings are
instantiated as "truth of the `i`-th formula in `s` on the tuple's
underlying function". -/
theorem indiscernibleSequence_of_pureColoring
    {L' : Language.{0, 0}}
    (hPure : PureColoringHypothesis) :
    IndiscernibleSequenceHypothesis (L' := L') := by
  classical
  intro s M _ instLinOrd hSize
  -- Each coloring: a tuple `t : Fin (s i).1 ↪o M` is colored by the
  -- `Bool` cast of the truth of `(s i).2` on the underlying function `⇑t`.
  let c : ℕ → Σ n, (Fin n ↪o M) → Bool := fun i =>
    ⟨(s i).1, fun t => decide (((s i).2).Realize (Empty.elim : Empty → M) (⇑t))⟩
  obtain ⟨f, hfMono, hfConst⟩ := hPure M hSize c
  refine ⟨f, hfMono, ?_⟩
  intro n φ ⟨i, hi⟩ t t' ht ht' htR ht'R
  -- Goal (after unfolding `id ∘ _ = _`):
  --   φ.Realize Empty.elim t ↔ φ.Realize Empty.elim t'
  show φ.Realize (Empty.elim : Empty → M) (id ∘ t) ↔
       φ.Realize (Empty.elim : Empty → M) (id ∘ t')
  have hidt : (id ∘ t : Fin n → M) = t := rfl
  have hidt' : (id ∘ t' : Fin n → M) = t' := rfl
  rw [hidt, hidt']
  -- Apply the pure hypothesis at the coloring for `i`.
  -- `hi : s i = ⟨n, φ⟩` determines `(c i).1 = n` and `(c i).2` in terms of `φ`.
  have hnEq : (c i).1 = n := by simp [c, hi]
  -- Bundle `t` and `t'` as order-embeddings of type `Fin (c i).1 ↪o M`.
  let tC : Fin (c i).1 ↪o M :=
    hnEq ▸ OrderEmbedding.ofStrictMono t ht
  let t'C : Fin (c i).1 ↪o M :=
    hnEq ▸ OrderEmbedding.ofStrictMono t' ht'
  -- Membership in `Set.range f` transports through `hnEq`.
  have htCR : ∀ k, tC k ∈ Set.range f := by
    intro k; simp only [tC]; cases hnEq; exact htR k
  have ht'CR : ∀ k, t'C k ∈ Set.range f := by
    intro k; simp only [t'C]; cases hnEq; exact ht'R k
  -- The pure-coloring conclusion.
  have hbool : (c i).2 tC = (c i).2 t'C := hfConst i tC t'C htCR ht'CR
  -- Decode: after `cases hnEq`, (c i).1 identifies with n. Unfold `c` and
  -- reduce the embedding coercions; extract `(s i).snd = φ` via
  -- Sigma-injection on `hi` (the fst-transport is `rfl` by definition).
  cases hnEq
  simp only [c, tC, t'C, OrderEmbedding.coe_ofStrictMono] at hbool
  -- `(s i).snd = φ` via Sigma-injection on `hi`. The first-component
  -- equality is definitional ((s i).fst = (c i).fst by c's def), so the
  -- `HEq` on the second component reduces to regular `Eq`.
  have hi_eta : (⟨(s i).fst, (s i).snd⟩ : Σ n, L'.BoundedFormulaω Empty n) =
      ⟨(c i).fst, φ⟩ := hi
  obtain ⟨_, h_snd⟩ := Sigma.mk.inj_iff.mp hi_eta
  rw [eq_of_heq h_snd] at hbool
  exact decide_eq_decide.mp hbool

end Language

end FirstOrder
