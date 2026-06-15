/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.Hanf
import InfinitaryLogic.Methods.EM.FragmentAdapter
import InfinitaryLogic.Methods.EM.TailAdapter
import InfinitaryLogic.Methods.EM.Extraction
import InfinitaryLogic.Combinatorics.InfiniteRamseyFamily

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

/-! ### Tail-weakened residual

The interface-refinement audit (2026-06-10) showed that the EM stretching pipeline consumes
source-side indiscernibility only through the finite-satisfiability lemma, where the
interpreting tuple is freely chosen — so per-formula **tail** indiscernibility suffices
(see `Methods/EM/TailAdapter.lean`). The tail residual below matches what classical
Erdős–Rado extraction actually produces in the source model (per-arity cutoffs, no full
simultaneity across arities), and is implied by the original `MorleyHanfExtraction`. -/

/-- **Tail-weakened residual extraction hypothesis.** Like `MorleyHanfExtraction`, but the
extracted sequence is only required to be *tail*-indiscernible on the family: for each
formula there is a cutoff beyond which all strictly monotone tuples agree. This is the
form a per-arity Erdős–Rado schedule produces. -/
def MorleyHanfExtractionTail : Prop :=
  ∀ (s : ℕ → Σ n, L'.BoundedFormulaω Empty n) (M : Type) [L'.Structure M],
    Cardinal.mk M ≥ Cardinal.beth (Ordinal.omega 1) →
    ∃ (a : ℕ → M),
      (∀ i j : ℕ, i ≠ j → a i ≠ a j) ∧
      IsLomega1omegaIndiscernibleOnTail a (Set.range s)

omit [Countable (Σ l, L'.Relations l)] in
/-- **`MorleyHanfExtractionTail` holds (cheap route, modulo `infinite_ramsey_nat_family`).**

The tail residual is dischargeable from a merely countably-infinite source — the `ℶ_{ω₁}`
hypothesis is not consumed. Because the colorings are `Bool`-per-formula and the tail cutoff is
per-formula, the extraction is an *infinite Ramsey* fact on `ℕ`, not an Erdős–Rado/beth-schedule
theorem:

* take an injective `a : ℕ → M` (`Infinite.natEmbedding`; no order on `M` is needed — the
  formula realization ignores it, the "increasing tuple" structure lives entirely in the `ℕ`
  index);
* pull each formula's truth back to a `Bool` coloring of strictly-increasing `ℕ`-tuples;
* apply the countable-family diagonal Ramsey theorem `infinite_ramsey_nat_family` to obtain a
  single `g : ℕ ↪o ℕ` that is eventually homogeneous for every coloring;
* read off pairwise-distinctness (injectivity) and per-formula tail indiscernibility of
  `a ∘ g`.

The `ℶ_{ω₁}` beth schedule is a strictly stronger statement (full/uncountable indiscernibility),
not required by this bridge. -/
theorem morleyHanfExtractionTail_holds : MorleyHanfExtractionTail (L' := L') := by
  classical
  intro s M instM hSize
  -- `M` is infinite: `ℵ₀ ≤ ℶ_{ω₁} ≤ #M`.
  haveI : Infinite M := by
    rw [Cardinal.infinite_iff]
    exact le_trans (Cardinal.aleph0_le_beth _) hSize
  -- Injective base sequence `a : ℕ → M` (no order on `M` is needed).
  let a : ℕ → M := Infinite.natEmbedding M
  have ha_inj : Function.Injective a := (Infinite.natEmbedding M).injective
  -- Pull each formula's truth back to a `Bool` coloring of strictly-increasing `ℕ`-tuples.
  let c : ℕ → Σ n, (Fin n ↪o ℕ) → Bool := fun i =>
    ⟨(s i).1, fun t => decide ((s i).2.Realize (Empty.elim : Empty → M) (fun k => a (t k)))⟩
  obtain ⟨g, hg⟩ := infinite_ramsey_nat_family c
  refine ⟨a ∘ g, ?_, ?_⟩
  · -- Pairwise distinct.
    intro i j hij h
    exact hij (g.injective (ha_inj h))
  · -- Tail indiscernible on `Set.range s`.
    intro n φ hmem
    obtain ⟨i, hi⟩ := hmem
    obtain ⟨N, hN⟩ := hg i
    refine ⟨N, ?_⟩
    intro u v hu hv hu_deep hv_deep
    -- Arity transport: `(c i).1 = n`.
    have hnEq : (c i).1 = n := by simp [c, hi]
    let uC : Fin (c i).1 ↪o ℕ := hnEq ▸ OrderEmbedding.ofStrictMono u hu
    let vC : Fin (c i).1 ↪o ℕ := hnEq ▸ OrderEmbedding.ofStrictMono v hv
    have huCdeep : ∀ k, N ≤ uC k := by intro k; simp only [uC]; cases hnEq; exact hu_deep k
    have hvCdeep : ∀ k, N ≤ vC k := by intro k; simp only [vC]; cases hnEq; exact hv_deep k
    have hbool : (c i).2 (uC.trans g) = (c i).2 (vC.trans g) := hN uC vC huCdeep hvCdeep
    -- Decode the `Bool` equation back to a truth equivalence for `φ`.
    cases hnEq
    simp only [c, uC, vC, RelEmbedding.trans_apply, OrderEmbedding.coe_ofStrictMono] at hbool
    have hi_eta : (⟨(s i).fst, (s i).snd⟩ : Σ n, L'.BoundedFormulaω Empty n) =
        ⟨(c i).fst, φ⟩ := hi
    obtain ⟨_, h_snd⟩ := Sigma.mk.inj_iff.mp hi_eta
    rw [eq_of_heq h_snd] at hbool
    show φ.Realize (Empty.elim : Empty → M) ((a ∘ g) ∘ u) ↔
         φ.Realize (Empty.elim : Empty → M) ((a ∘ g) ∘ v)
    exact decide_eq_decide.mp hbool

omit [Countable (Σ l, L'.Relations l)] in
/-- The original (full-indiscernibility) residual implies the tail residual. -/
theorem morleyHanfExtractionTail_of_morleyHanfExtraction
    (h : MorleyHanfExtraction (L' := L')) : MorleyHanfExtractionTail (L' := L') := by
  intro s M _ hSize
  obtain ⟨a, hPair, hInd⟩ := h s M hSize
  exact ⟨a, hPair, hInd.isLomega1omegaIndiscernibleOnTail⟩

/-- **The honest residual consumed by the tail Morley–Hanf bridge.** From a tail-indiscernible
sequence in a model of size `≥ ℶ_ω₁`, the EM tail-template theory is realizable over every target
order `J`.

The `|M| ≥ ℶ_ω₁` premise is essential for the statement to be **true-shaped**: the bridge's
template theory is `{φ} ∪ {distinct constants}`, so realizability over a size-`κ` order is "`φ`
has a model of size `≥ κ`". Without the cardinality premise this would assert that *every* `φ`
with an infinite model has arbitrarily large models — false for Scott sentences of bounded Hanf
number. With it, the statement is classically true (it is the model-existence half of
Morley–Hanf, realized by the Ehrenfeucht–Mostowski / Skolem-hull construction over `J`).

Strictly weaker than the broad `L_{ω₁ω}` compactness oracle: it asks for realizability only of
the specific finitely-satisfiable EM template theories (finite satisfiability is the proved
`IsLomega1omegaIndiscernibleOnTail.templateTheoryOn_finitelySatisfiable`), from a large source —
not full `L_{ω₁ω}` compactness (false in general). The genuine remaining non-formal content for
this bridge is exactly its proof: the EM construction. -/
def TailTemplateRealizable : Prop :=
  ∀ (s : ℕ → Σ n, L'.BoundedFormulaω Empty n) (M : Type) [L'.Structure M] (a : ℕ → M)
    (J : Type) [LinearOrder J],
    Cardinal.mk M ≥ Cardinal.beth (Ordinal.omega 1) →
    IsLomega1omegaIndiscernibleOnTail a (Set.range s) →
    ∃ (N : Type) (_ : L'[[J]].Structure N),
      Theoryω.Model
        ((tailTemplateOfSeq a : Lomega1omegaTemplate L').templateTheoryOfSeq s J) N

omit [Countable (Σ l, L'.Relations l)] in
/-- The broad per-target compactness oracle implies the honest tail-template realizability
residual: apply compactness to the (finitely-satisfiable) tail-template theory itself. Witnesses
that `TailTemplateRealizable` is genuinely weaker than full compactness. -/
theorem tailTemplateRealizable_of_compact
    (hCompact : ∀ (J : Type) [LinearOrder J] (S : Set L'[[J]].Sentenceω),
      (∀ F : Set L'[[J]].Sentenceω, F.Finite → F ⊆ S →
        ∃ (N : Type) (_ : L'[[J]].Structure N), Theoryω.Model F N) →
      ∃ (N : Type) (_ : L'[[J]].Structure N), Theoryω.Model S N) :
    TailTemplateRealizable (L' := L') := by
  intro s M instM a J instJ _hSize hIndisc
  exact hIndisc.templateTheoryOfSeq_model_of_compact s
    (Order.succ (Ordinal.omega0 : Ordinal.{0}))
    (Order.lt_succ (Ordinal.omega0 : Ordinal.{0})) (hCompact J)

omit [Countable (Σ l, L'.Relations l)] in
/-- **Morley–Hanf via tail extraction + template realizability** (proved).

The honest tail bridge: the residual extraction produces a tail-indiscernible sequence, and the
EM template theory it generates is realized via the weakest-honest residual
`TailTemplateRealizable` — NOT a broad `L_{ω₁ω}` compactness oracle. Same proof shape, through
the model-form stretching of `Methods/EM/TailAdapter.lean`. -/
@[blueprint "thm:morley-hanf-tail"
  (title := /-- Morley-Hanf via tail extraction -/)
  (statement := /-- Assuming tail-restricted source-side extraction and realizability of the
    EM tail-template theory, every Lω₁ω sentence satisfied in a model of size
    $\geq \beth_{\omegaone}$ has arbitrarily large models. -/)
  (proof := /-- Extract a pairwise-distinct ℕ-indexed sequence tail-indiscernible on the
    family $\{\varphi, x_0 \neq x_1\}$, stretch along an ordinal of the target cardinality
    through the eventually-form template realized by the residual, and read off $\varphi$
    preservation and injectivity from the sequence-form equivalence. -/)
  (uses := ["def:arb-large-models"])]
theorem hasArbLargeModels_of_tail_realizability
    (hExtract : MorleyHanfExtractionTail (L' := L'))
    (hRealize : TailTemplateRealizable (L' := L'))
    (φ : L'.Sentenceω)
    (hφ : ∃ (M : Type) (_ : L'.Structure M), Sentenceω.Realize φ M ∧
      Cardinal.mk M ≥ Cardinal.beth (Ordinal.omega 1)) :
    HasArbLargeModels φ := by
  classical
  obtain ⟨M, instM, hRealizeM, hSizeM⟩ := hφ
  let s : ℕ → Σ n, L'.BoundedFormulaω Empty n := fun i =>
    match i with
    | 0 => ⟨0, φ⟩
    | 1 => ⟨2, disEqFormula⟩
    | _ + 2 => ⟨0, φ⟩
  have hs0 : s 0 = ⟨0, φ⟩ := rfl
  have hs1 : s 1 = ⟨2, disEqFormula⟩ := rfl
  obtain ⟨a, hPairwise, hIndisc⟩ := hExtract s M hSizeM
  intro κ
  let J : Type := (Cardinal.ord κ).ToType
  haveI : LinearOrder J := linearOrder_toType _
  have hJ_card : Cardinal.mk J = κ := Cardinal.mk_ord_toType κ
  obtain ⟨N, instN, b, hSeq⟩ :=
    IsLomega1omegaIndiscernibleOnTail.stretch_restricted_sequence_of_model (J := J)
      s (hRealize s M a J hSizeM hIndisc)
  letI : L'.Structure N := (L'.lhomWithConstants J).reduct N
  refine ⟨N, inferInstance, ?_, ?_⟩
  · -- Sentence preservation
    have hSeq_at_0 := hSeq 0
    rw [hs0] at hSeq_at_0
    dsimp only at hSeq_at_0
    let t0 : Fin 0 ↪o J :=
      ⟨⟨Fin.elim0, fun ⟨_, hk⟩ => absurd hk (Nat.not_lt_zero _)⟩, fun {x} => x.elim0⟩
    have hkey := hSeq_at_0 t0
    have hbt0 : (b ∘ t0 : Fin 0 → N) = Fin.elim0 := funext fun k => k.elim0
    rw [hbt0] at hkey
    have hTmpl : (tailTemplateOfSeq a : Lomega1omegaTemplate L').truth φ := by
      refine ⟨0, fun u _ _ => ?_⟩
      have hu0 : (a ∘ u : Fin 0 → M) = Fin.elim0 := funext fun k => k.elim0
      rw [hu0]
      exact hRealizeM
    show Sentenceω.Realize φ N
    exact hkey.mpr hTmpl
  · -- Injectivity ⇒ #N ≥ #J = κ
    have hDisTruth : (tailTemplateOfSeq a : Lomega1omegaTemplate L').truth disEqFormula := by
      refine ⟨0, fun u hu _ => ?_⟩
      simp only [disEqFormula, BoundedFormulaω.realize_not, BoundedFormulaω.realize_equal,
        Term.realize_var]
      intro heq
      have h01 : u 0 ≠ u 1 := ne_of_lt (hu (show (0 : Fin 2) < 1 by decide))
      exact hPairwise (u 0) (u 1) h01 (by simpa using heq)
    have hSeq_at_1 := hSeq 1
    rw [hs1] at hSeq_at_1
    dsimp only at hSeq_at_1
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
        rw [h0, h1]
        exact heq
      intro j j' hbjj'
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact helper hlt hbjj'
      · exact helper hlt hbjj'.symm
    calc Cardinal.mk N ≥ Cardinal.mk J := Cardinal.mk_le_of_injective hbInj
      _ = κ := hJ_card

omit [Countable (Σ l, L'.Relations l)] in
/-- **Legacy: Morley–Hanf via tail extraction + a broad compactness oracle.** Kept for
compatibility. The compactness oracle is *stronger than needed*: it asserts full `L_{ω₁ω}`
compactness for every `L'[[J]]`, which is false in general. It factors through the honest
residual via `tailTemplateRealizable_of_compact`. Prefer
`hasArbLargeModels_of_tail_realizability`. -/
theorem hasArbLargeModels_of_tail_extraction
    (hExtract : MorleyHanfExtractionTail (L' := L'))
    (hCompact : ∀ (J : Type) [LinearOrder J] (S : Set L'[[J]].Sentenceω),
      (∀ F : Set L'[[J]].Sentenceω, F.Finite → F ⊆ S →
        ∃ (N : Type) (_ : L'[[J]].Structure N), Theoryω.Model F N) →
      ∃ (N : Type) (_ : L'[[J]].Structure N), Theoryω.Model S N)
    (φ : L'.Sentenceω)
    (hφ : ∃ (M : Type) (_ : L'.Structure M), Sentenceω.Realize φ M ∧
      Cardinal.mk M ≥ Cardinal.beth (Ordinal.omega 1)) :
    HasArbLargeModels φ :=
  hasArbLargeModels_of_tail_realizability hExtract
    (tailTemplateRealizable_of_compact hCompact) φ hφ

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
    (M : Type) [L'.Structure M] (_ : LinearOrder M) (_ : WellFoundedLT M),
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
  -- Equip `M` with a canonical well-ordering via `exists_wellOrder`,
  -- which provides both a `LinearOrder` and `WellFoundedLT` on `M`.
  obtain ⟨instLO, instWF⟩ := exists_wellOrder M
  letI : LinearOrder M := instLO
  obtain ⟨f, hfMono, hfInd⟩ := hSeq s M instLO instWF hSize
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

/-- **Pure partition-calculus residual**: for every well-ordered type
`I` with `|I| ≥ ℶ_ω₁` and every countable family of Bool-valued
colorings on finite-arity increasing tuples (order-embeddings) from
`I`, there exists an infinite strictly-monotone `ℕ → I` sequence whose
range is monochromatic for every coloring in the family.

The body mentions no language, no structure, no formula — only a
well-ordered source (`LinearOrder I` + `WellFoundedLT I`), cardinalities,
`ℕ`-indexed arities, and `Bool` colorings on `Fin n ↪o I`. This is the
Erdős–Rado statement proper; Phase 2d targets it directly.
`indiscernibleSequence_of_pureColoring` below proves that this implies
the larger `IndiscernibleSequenceHypothesis`.

Note on the well-ordering assumption: arbitrary `LinearOrder I` does not
admit strict-monotone `ℕ → I` in general (counterexample: `I = ℕ` with
opposite order). The consumer chain always provides `I` as a canonical
well-ordering of a model's carrier (via `WellOrderingRel`), so
`WellFoundedLT I` is the right strengthening. -/
def PureColoringHypothesis : Prop :=
  ∀ (I : Type) [LinearOrder I] [WellFoundedLT I],
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
  intro s M _ instLinOrd instWF hSize
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

/-! ### Compact-only Morley–Hanf headlines

These wrappers collapse the proved reduction chain
(`hasArbLargeModels_of_restricted_extraction` ∘
`morleyHanfExtraction_of_indiscernibleSequence` ∘
`indiscernibleSequence_of_pureColoring`) into a single theorem parameterized
by the pure combinatorial hypothesis and a compactness oracle.

When Phase 2d2 discharges `PureColoringHypothesis` via the Erdős–Rado
theorem in `InfinitaryLogic/Combinatorics/ErdosRado.lean`, the
`hPure` argument becomes a theorem rather than a hypothesis, and the
wrappers below lose it — producing an unconditional
`hasArbLargeModels_of_compact` and `morley_hanf_of_compact`. -/

/-- **Morley–Hanf reduction**: assuming the pure combinatorial hypothesis
`PureColoringHypothesis` and a per-target compactness oracle for every
`L'[[J]]`, any sentence satisfied in a model of size ≥ ℶ_ω₁ has
arbitrarily large models.

Composes the proved chain:
  `hPure → IndiscernibleSequenceHypothesis → MorleyHanfExtraction →
   HasArbLargeModels φ`. -/
theorem hasArbLargeModels_of_pureColoring_and_compact
    {L' : Language.{0, 0}} [Countable (Σ l, L'.Relations l)]
    (hPure : PureColoringHypothesis)
    (hCompact : ∀ (J : Type) [LinearOrder J] (S : Set L'[[J]].Sentenceω),
      (∀ F : Set L'[[J]].Sentenceω, F.Finite → F ⊆ S →
        ∃ (N : Type) (_ : L'[[J]].Structure N), Theoryω.Model F N) →
      ∃ (N : Type) (_ : L'[[J]].Structure N), Theoryω.Model S N)
    (φ : L'.Sentenceω)
    (hφ : ∃ (M : Type) (_ : L'.Structure M), Sentenceω.Realize φ M ∧
      Cardinal.mk M ≥ Cardinal.beth (Ordinal.omega 1)) :
    HasArbLargeModels φ :=
  hasArbLargeModels_of_restricted_extraction
    (morleyHanfExtraction_of_indiscernibleSequence
      (indiscernibleSequence_of_pureColoring hPure))
    hCompact φ hφ

/-- **Morley–Hanf bound (compact + pure-coloring form)**: `ℶ_ω₁` is a
Hanf bound for every Lω₁ω sentence, assuming the pure partition-calculus
hypothesis and a compactness oracle.

Specializes `hasArbLargeModels_of_pureColoring_and_compact` to the
`IsHanfBound` shape used as the canonical Morley–Hanf endpoint. -/
theorem morley_hanf_of_pureColoring_and_compact
    {L' : Language.{0, 0}} [Countable (Σ l, L'.Relations l)]
    (hPure : PureColoringHypothesis)
    (hCompact : ∀ (J : Type) [LinearOrder J] (S : Set L'[[J]].Sentenceω),
      (∀ F : Set L'[[J]].Sentenceω, F.Finite → F ⊆ S →
        ∃ (N : Type) (_ : L'[[J]].Structure N), Theoryω.Model F N) →
      ∃ (N : Type) (_ : L'[[J]].Structure N), Theoryω.Model S N)
    (φ : L'.Sentenceω) :
    IsHanfBound φ (Cardinal.beth (Ordinal.omega 1)) := by
  intro ⟨M, hStr, hRealize, hSize⟩
  exact hasArbLargeModels_of_pureColoring_and_compact hPure hCompact φ
    ⟨M, hStr, hRealize, hSize⟩

/-! ### Realizability-only Morley–Hanf via the proved tail extraction

The tail-weakened source extraction is now **formalized** (`morleyHanfExtractionTail_holds`,
proved from `infinite_ramsey_nat_family` — countable Ramsey on `ℕ`, not an `ℶ_{ω₁}` Erdős–Rado
schedule). Composing it with `hasArbLargeModels_of_tail_realizability` discharges the
combinatorial hypothesis entirely: the headline below takes **only** the honest residual
`TailTemplateRealizable` (realizability of the EM tail-template theory). So for this bridge the
sole remaining non-formal content is that template realizability — whose honest proof is the
classical Ehrenfeucht–Mostowski / Skolem-hull construction — **not** source extraction, **not**
the beth partition calculus, and **not** full `L_{ω₁ω}` compactness (false in general). The
`*_compact` wrappers are retained as legacy; their oracle is strictly stronger than needed. -/

/-- **Morley–Hanf reduction (realizability-only, extraction discharged)**: assuming only the
honest residual `TailTemplateRealizable`, any sentence satisfied in a model of size ≥ ℶ_ω₁ has
arbitrarily large models. Source extraction is the proved `morleyHanfExtractionTail_holds`; no
combinatorial hypothesis, no compactness oracle. -/
theorem hasArbLargeModels_of_tail_realizable
    {L' : Language.{0, 0}}
    (hRealize : TailTemplateRealizable (L' := L'))
    (φ : L'.Sentenceω)
    (hφ : ∃ (M : Type) (_ : L'.Structure M), Sentenceω.Realize φ M ∧
      Cardinal.mk M ≥ Cardinal.beth (Ordinal.omega 1)) :
    HasArbLargeModels φ :=
  hasArbLargeModels_of_tail_realizability (morleyHanfExtractionTail_holds (L' := L')) hRealize φ hφ

/-- **Morley–Hanf bound (realizability-only, extraction discharged)**: `ℶ_ω₁` is a Hanf bound for
every Lω₁ω sentence, assuming only `TailTemplateRealizable`. This is the project's tightest
Morley–Hanf endpoint — the only non-formal input is realizing the EM tail-template theory. -/
theorem morley_hanf_of_tail_realizable
    {L' : Language.{0, 0}}
    (hRealize : TailTemplateRealizable (L' := L'))
    (φ : L'.Sentenceω) :
    IsHanfBound φ (Cardinal.beth (Ordinal.omega 1)) := by
  intro ⟨M, hStr, hRealizeφ, hSize⟩
  exact hasArbLargeModels_of_tail_realizable hRealize φ ⟨M, hStr, hRealizeφ, hSize⟩

/-- **Legacy (compact-only): Morley–Hanf reduction via a broad compactness oracle.** Retained for
compatibility; the per-target compactness oracle is strictly stronger than the honest residual
`TailTemplateRealizable` (see `tailTemplateRealizable_of_compact`) and asserts full `L_{ω₁ω}`
compactness, which is false in general. Prefer `hasArbLargeModels_of_tail_realizable`. -/
theorem hasArbLargeModels_of_tail_compact
    {L' : Language.{0, 0}}
    (hCompact : ∀ (J : Type) [LinearOrder J] (S : Set L'[[J]].Sentenceω),
      (∀ F : Set L'[[J]].Sentenceω, F.Finite → F ⊆ S →
        ∃ (N : Type) (_ : L'[[J]].Structure N), Theoryω.Model F N) →
      ∃ (N : Type) (_ : L'[[J]].Structure N), Theoryω.Model S N)
    (φ : L'.Sentenceω)
    (hφ : ∃ (M : Type) (_ : L'.Structure M), Sentenceω.Realize φ M ∧
      Cardinal.mk M ≥ Cardinal.beth (Ordinal.omega 1)) :
    HasArbLargeModels φ :=
  hasArbLargeModels_of_tail_realizable (tailTemplateRealizable_of_compact hCompact) φ hφ

/-- **Legacy (compact-only): Morley–Hanf bound via a broad compactness oracle.** Prefer
`morley_hanf_of_tail_realizable`. -/
theorem morley_hanf_of_tail_compact
    {L' : Language.{0, 0}}
    (hCompact : ∀ (J : Type) [LinearOrder J] (S : Set L'[[J]].Sentenceω),
      (∀ F : Set L'[[J]].Sentenceω, F.Finite → F ⊆ S →
        ∃ (N : Type) (_ : L'[[J]].Structure N), Theoryω.Model F N) →
      ∃ (N : Type) (_ : L'[[J]].Structure N), Theoryω.Model S N)
    (φ : L'.Sentenceω) :
    IsHanfBound φ (Cardinal.beth (Ordinal.omega 1)) := by
  intro ⟨M, hStr, hRealize, hSize⟩
  exact hasArbLargeModels_of_tail_compact hCompact φ ⟨M, hStr, hRealize, hSize⟩

end Language

end FirstOrder
