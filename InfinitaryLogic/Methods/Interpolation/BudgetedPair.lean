/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.Interpolation.QuantifierRoundTrip
import InfinitaryLogic.Methods.Interpolation.PairedInsepFamily
import InfinitaryLogic.Lomega1omega.QuantifierOccurrence

/-!
# The budgeted labelled pair (issue #15, side-labelled restart)

The certificate selected by `docs/malitz-source-reconstruction-2.md`: Feferman's Theorem 4.3 keeps the
two sides **labelled** — formulas are retained on their derivational side, never reprojected by
vocabulary — and carries three conditions along the derivation beside the two entailments:

* the **shared vocabulary** condition on the separator;
* the **shared constant** condition, `sentenceJConsts θ ⊆ theoryJConsts Γ ∩ theoryJConsts Δ`
  (Feferman's `Free₀(θ) ⊆ Free₀(ϕ) ∩ Free₀(ψ)`, in the constant presentation);
* the **two quantifier permissions**, `hasQuantSigned true θ → HasQuantSigned true Γ` and
  `hasQuantSigned false θ → HasQuantSigned true Δ`.

The second permission reads `true` on the right because `Δ` holds the **negated** consequent: at the
root `Un({r₂.not}) = Ex(r₂)`.

The shared-constant condition is **primary**, not derived from the permissions.  That is the source's
own account: "in building up an interpolant following a cut-free derivation … we are forced to
introduce quantifiers into the interpolant only as required to maintain the condition (iii), and that
turns out to lead to (iv)" (Feferman, *"Ah, Chu!"*, pp. 2–3).  The earlier `FefermanAllowed` had the
dependency backwards, charging constants into the permissions as a standing assumption.

Everything the canonical-projection experiment needed disappears here.  A fresh witness constant is
added to **one** labelled side; being absent from the other, the shared-constant condition forbids the
separator from mentioning it, so the separator **transports unchanged** — no `genEx`, no `genAll`, no
support parameter to strip, no projection coverage, and no root tags.  Quantifier non-growth is
likewise immediate, because the quantified parent already sits on the same labelled side.

`Methods/Interpolation/FefermanProjection.lean` is **not imported**: it is retained as experimental
evidence for the canonical-projection route and its C1 failure, not as a dependency.

## Provenance

The labelled architecture is **source-backed** by Feferman's split-sequent proof, which he describes
explicitly.  The *semantic consistency-property* implementation below is this repository's adaptation:
Stern's model-theoretic forcing proof is identified as the semantic dual, but its exact invariant is
**unverified** — the paper has not been read.
-/

namespace FirstOrder.Language

open FirstOrder Structure BoundedFormulaω

variable {L : Language.{0, 0}} {M : Type}

/-! ## The constant support of a labelled side -/

/-- The Henkin constants occurring anywhere in a set of sentences. -/
def theoryJConsts (T : Set L[[ℕ]].Sentenceω) : Set ℕ :=
  ⋃ σ ∈ T, sentenceJConsts (L' := L) (J := ℕ) σ

variable {T T' : Set L[[ℕ]].Sentenceω} {σ : L[[ℕ]].Sentenceω} {c : ℕ}

theorem sentenceJConsts_subset_theoryJConsts (hmem : σ ∈ T) :
    sentenceJConsts (L' := L) (J := ℕ) σ ⊆ theoryJConsts T :=
  Set.subset_biUnion_of_mem hmem

theorem theoryJConsts_mono (h : T ⊆ T') : theoryJConsts (L := L) T ⊆ theoryJConsts T' := by
  intro k hk
  simp only [theoryJConsts, Set.mem_iUnion] at hk ⊢
  obtain ⟨ρ, hρ, hk⟩ := hk
  exact ⟨ρ, h hρ, hk⟩

@[simp] theorem theoryJConsts_insert :
    theoryJConsts (L := L) (insert σ T)
      = sentenceJConsts (L' := L) (J := ℕ) σ ∪ theoryJConsts T := by
  ext k
  simp only [theoryJConsts, Set.mem_iUnion, Set.mem_insert_iff, Set.mem_union]
  constructor
  · rintro ⟨ρ, rfl | hρ, hk⟩
    · exact Or.inl hk
    · exact Or.inr ⟨ρ, hρ, hk⟩
  · rintro (hk | ⟨ρ, hρ, hk⟩)
    · exact ⟨σ, Or.inl rfl, hk⟩
    · exact ⟨ρ, Or.inr hρ, hk⟩

/-- **Insertion non-growth for constants**: inserting a sentence whose constants the side already
carries does not enlarge the side's support.  Every branch rule needs exactly this. -/
theorem theoryJConsts_insert_of_subset
    (h : sentenceJConsts (L' := L) (J := ℕ) σ ⊆ theoryJConsts T) :
    theoryJConsts (L := L) (insert σ T) = theoryJConsts T := by
  rw [theoryJConsts_insert, Set.union_eq_self_of_subset_left h]

/-- Freshness for a side is exactly non-membership in its support. -/
theorem notMem_theoryJConsts_iff :
    c ∉ theoryJConsts (L := L) T ↔ ∀ γ ∈ T, c ∉ sentenceJConsts (L' := L) (J := ℕ) γ := by
  constructor
  · intro h γ hγ hk
    exact h (sentenceJConsts_subset_theoryJConsts hγ hk)
  · intro h hk
    simp only [theoryJConsts, Set.mem_iUnion] at hk
    obtain ⟨γ, hγ, hk⟩ := hk
    exact h γ hγ hk

/-! ## The certificate -/

variable {F₁ F₂ : Set (Σ n, L.Functions n)} {R₁ R₂ : Set (Σ n, L.Relations n)}
  {Γ Δ : Set L[[ℕ]].Sentenceω}

/-- **A budgeted separator of the labelled pair `(Γ, Δ)`.**  Five conditions: the two entailments, the
shared vocabulary, the **shared constants**, and the two quantifier permissions. -/
def BudgetedPairSeparates (F₁ : Set (Σ n, L.Functions n)) (R₁ : Set (Σ n, L.Relations n))
    (F₂ : Set (Σ n, L.Functions n)) (R₂ : Set (Σ n, L.Relations n))
    (Γ Δ : Set L[[ℕ]].Sentenceω) (θ : L[[ℕ]].Sentenceω) : Prop :=
  Theoryω.Entails Γ θ ∧
  Theoryω.Entails Δ θ.not ∧
  θ ∈ SentBnd (F₁ ∩ F₂) (R₁ ∩ R₂) ∧
  sentenceJConsts (L' := L) (J := ℕ) θ ⊆ theoryJConsts Γ ∩ theoryJConsts Δ ∧
  (hasQuantSigned true θ → Theoryω.HasQuantSigned true Γ) ∧
  (hasQuantSigned false θ → Theoryω.HasQuantSigned true Δ)

/-- **The invariant**: the labelled pair admits no budgeted separator. -/
def BudgetedPairInsep (F₁ : Set (Σ n, L.Functions n)) (R₁ : Set (Σ n, L.Relations n))
    (F₂ : Set (Σ n, L.Functions n)) (R₂ : Set (Σ n, L.Relations n))
    (Γ Δ : Set L[[ℕ]].Sentenceω) : Prop :=
  ¬ ∃ θ, BudgetedPairSeparates F₁ R₁ F₂ R₂ Γ Δ θ

/-! ## C0 — the mixed contradiction gate

The diagnostic case for the labelled architecture: a sentence on the left with its negation on the
right.  All five conditions are paid by the two memberships themselves. -/

/-- **Mixed C0.**  If `σ ∈ Γ` and `σ.not ∈ Δ` then `σ` *is* a budgeted separator: its vocabulary is
shared because the two sides bound the same sentence, its constants occur in both, its universal
occurrences are paid by `Γ`, and its existential occurrences are paid by the **universal** occurrences
of `σ.not` in `Δ`. -/
theorem not_budgetedPairInsep_of_mixed (hΓ : Γ ⊆ SentBnd F₁ R₁) (hΔ : Δ ⊆ SentBnd F₂ R₂)
    (hσΓ : σ ∈ Γ) (hσΔ : σ.not ∈ Δ) : ¬ BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ := by
  intro h
  have hb₁ : σ ∈ SentBnd (L := L) F₁ R₁ := hΓ hσΓ
  have hb₂ : σ ∈ SentBnd (L := L) F₂ R₂ := sentBnd_not_iff.mp (hΔ hσΔ)
  refine h ⟨σ, Theoryω.entails_of_mem hσΓ, Theoryω.entails_of_mem hσΔ,
    ⟨Set.subset_inter hb₁.1 hb₂.1, Set.subset_inter hb₁.2 hb₂.2⟩, ?_, ?_, ?_⟩
  · refine Set.subset_inter (sentenceJConsts_subset_theoryJConsts hσΓ) ?_
    rw [← sentenceJConsts_not (L' := L) σ]
    exact sentenceJConsts_subset_theoryJConsts hσΔ
  · exact fun hq => Theoryω.hasQuantSigned_of_mem hσΓ hq
  · intro hq
    exact Theoryω.hasQuantSigned_of_mem hσΔ ((hasQuantSigned_not true σ).mpr hq)

/-- **Same-side C0.**  A sentence and its negation on one side make it inconsistent, and the
quantifier-free, constant-free `⊥` (resp. `⊤`) separates. -/
theorem not_budgetedPairInsep_of_left_contradiction (hσ : σ ∈ Γ) (hnσ : σ.not ∈ Γ) :
    ¬ BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ := by
  intro h
  refine h ⟨BoundedFormulaω.falsum, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N instN _ hmodel
    have h1 := hmodel σ hσ
    have h2 := hmodel σ.not hnσ
    rw [Sentenceω.Realize, BoundedFormulaω.realize_not] at h2
    exact absurd h1 h2
  · intro N instN _ _
    rw [Sentenceω.Realize, BoundedFormulaω.realize_not]
    exact fun hf => hf
  · exact ⟨by rw [baseFunctionsIn_falsum]; exact Set.empty_subset _,
      by rw [show (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω).baseRelationsIn = ∅ from
        baseRelationsIn_falsum]; exact Set.empty_subset _⟩
  · rw [sentenceJConsts_falsum]; exact Set.empty_subset _
  · exact fun hq => absurd hq (hasQuantSigned_falsum true)
  · exact fun hq => absurd hq (hasQuantSigned_falsum false)

/-! ## C1 — implication branching

The source's rule verbatim: disjunction when the principal formula is on the **left**, conjunction
when on the **right**.  There is no leakage case to consider — the branch sentences join the side
their parent is on, and nowhere else. -/

/-- **C1, left.**  Separator `τ₁ ∨ τ₂`, written `(τ₁.not).imp τ₂`. -/
theorem budgetedPairInsep_imp_left (φ ψ : L[[ℕ]].Sentenceω) (hmem : φ.imp ψ ∈ Γ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ (insert φ.not Γ) Δ ∨
      BudgetedPairInsep F₁ R₁ F₂ R₂ (insert ψ Γ) Δ := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  simp only [BudgetedPairInsep, not_not] at h1 h2
  obtain ⟨τ₁, hE₁, hN₁, hb₁, hc₁, hu₁, hx₁⟩ := h1
  obtain ⟨τ₂, hE₂, hN₂, hb₂, hc₂, hu₂, hx₂⟩ := h2
  -- neither branch enlarges the left side's constant support or its universal budget
  have hcφ : theoryJConsts (L := L) (insert φ.not Γ) = theoryJConsts Γ :=
    theoryJConsts_insert_of_subset (by
      rw [sentenceJConsts_not]
      exact (sentenceJConsts_imp_left φ ψ).trans (sentenceJConsts_subset_theoryJConsts hmem))
  have hcψ : theoryJConsts (L := L) (insert ψ Γ) = theoryJConsts Γ :=
    theoryJConsts_insert_of_subset
      ((sentenceJConsts_imp_right φ ψ).trans (sentenceJConsts_subset_theoryJConsts hmem))
  have huφ : Theoryω.HasQuantSigned true (insert φ.not Γ) ↔ Theoryω.HasQuantSigned true Γ :=
    Theoryω.hasQuantSigned_insert_of_le fun hq =>
      Theoryω.hasQuantSigned_of_mem hmem (Or.inl ((hasQuantSigned_not true φ).mp hq))
  have huψ : Theoryω.HasQuantSigned true (insert ψ Γ) ↔ Theoryω.HasQuantSigned true Γ :=
    Theoryω.hasQuantSigned_insert_of_le fun hq => Theoryω.hasQuantSigned_of_mem hmem (Or.inr hq)
  rw [hcφ] at hc₁; rw [hcψ] at hc₂; rw [huφ] at hu₁; rw [huψ] at hu₂
  refine h ⟨(τ₁.not).imp τ₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- `Γ ⊨ τ₁ ∨ τ₂`, by the implication member
  · intro N instN neN hmodel
    rw [Sentenceω.Realize, BoundedFormulaω.realize_imp, BoundedFormulaω.realize_not]
    intro hnτ₁
    have hφtrue : @Sentenceω.Realize L[[ℕ]] φ N instN := by
      by_contra hnφ
      refine hnτ₁ (@hE₁ N instN neN fun ρ hρ => ?_)
      rcases Set.mem_insert_iff.mp hρ with rfl | hρ
      · rw [Sentenceω.Realize, BoundedFormulaω.realize_not]; exact hnφ
      · exact hmodel ρ hρ
    have himp := hmodel _ hmem
    rw [Sentenceω.Realize, BoundedFormulaω.realize_imp] at himp
    refine @hE₂ N instN neN fun ρ hρ => ?_
    rcases Set.mem_insert_iff.mp hρ with rfl | hρ
    · exact himp hφtrue
    · exact hmodel ρ hρ
  · intro N instN neN hmodel
    rw [Sentenceω.Realize, BoundedFormulaω.realize_not, BoundedFormulaω.realize_imp,
      BoundedFormulaω.realize_not]
    intro hcontra
    have hn₁ := @hN₁ N instN neN hmodel
    have hn₂ := @hN₂ N instN neN hmodel
    rw [Sentenceω.Realize, BoundedFormulaω.realize_not] at hn₁ hn₂
    exact hn₂ (hcontra hn₁)
  · exact ⟨baseFunctionsIn_imp_subset (by rw [baseFunctionsIn_not]; exact hb₁.1) hb₂.1,
      baseRelationsIn_imp_subset (by rw [baseRelationsIn_not]; exact hb₁.2) hb₂.2⟩
  · refine (sentenceJConsts_imp_subset ?_ hc₂)
    rw [sentenceJConsts_not]; exact hc₁
  · intro hq
    replace hq : hasQuantSigned true ((τ₁.not).imp τ₂) := hq
    rw [hasQuantSigned_imp, hasQuantSigned_not] at hq
    exact hq.elim hu₁ hu₂
  · intro hq
    replace hq : hasQuantSigned false ((τ₁.not).imp τ₂) := hq
    rw [hasQuantSigned_imp, hasQuantSigned_not] at hq
    exact hq.elim hx₁ hx₂

/-- **C1, right.**  Separator `τ₁ ∧ τ₂`. -/
theorem budgetedPairInsep_imp_right (φ ψ : L[[ℕ]].Sentenceω) (hmem : φ.imp ψ ∈ Δ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert φ.not Δ) ∨
      BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert ψ Δ) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  simp only [BudgetedPairInsep, not_not] at h1 h2
  obtain ⟨τ₁, hE₁, hN₁, hb₁, hc₁, hu₁, hx₁⟩ := h1
  obtain ⟨τ₂, hE₂, hN₂, hb₂, hc₂, hu₂, hx₂⟩ := h2
  have hcφ : theoryJConsts (L := L) (insert φ.not Δ) = theoryJConsts Δ :=
    theoryJConsts_insert_of_subset (by
      rw [sentenceJConsts_not]
      exact (sentenceJConsts_imp_left φ ψ).trans (sentenceJConsts_subset_theoryJConsts hmem))
  have hcψ : theoryJConsts (L := L) (insert ψ Δ) = theoryJConsts Δ :=
    theoryJConsts_insert_of_subset
      ((sentenceJConsts_imp_right φ ψ).trans (sentenceJConsts_subset_theoryJConsts hmem))
  have huφ : Theoryω.HasQuantSigned true (insert φ.not Δ) ↔ Theoryω.HasQuantSigned true Δ :=
    Theoryω.hasQuantSigned_insert_of_le fun hq =>
      Theoryω.hasQuantSigned_of_mem hmem (Or.inl ((hasQuantSigned_not true φ).mp hq))
  have huψ : Theoryω.HasQuantSigned true (insert ψ Δ) ↔ Theoryω.HasQuantSigned true Δ :=
    Theoryω.hasQuantSigned_insert_of_le fun hq => Theoryω.hasQuantSigned_of_mem hmem (Or.inr hq)
  rw [hcφ] at hc₁; rw [hcψ] at hc₂; rw [huφ] at hx₁; rw [huψ] at hx₂
  refine h ⟨τ₁.and τ₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N instN neN hmodel
    rw [Sentenceω.Realize, BoundedFormulaω.realize_and]
    exact ⟨@hE₁ N instN neN hmodel, @hE₂ N instN neN hmodel⟩
  · intro N instN neN hmodel
    rw [Sentenceω.Realize, BoundedFormulaω.realize_not, BoundedFormulaω.realize_and]
    have himp := hmodel _ hmem
    rw [Sentenceω.Realize, BoundedFormulaω.realize_imp] at himp
    by_cases hφtrue : @Sentenceω.Realize L[[ℕ]] φ N instN
    · have hn := @hN₂ N instN neN fun ρ hρ => by
        rcases Set.mem_insert_iff.mp hρ with rfl | hρ
        · exact himp hφtrue
        · exact hmodel ρ hρ
      rw [Sentenceω.Realize, BoundedFormulaω.realize_not] at hn
      exact fun hand => hn hand.2
    · have hn := @hN₁ N instN neN fun ρ hρ => by
        rcases Set.mem_insert_iff.mp hρ with rfl | hρ
        · rw [Sentenceω.Realize, BoundedFormulaω.realize_not]; exact hφtrue
        · exact hmodel ρ hρ
      rw [Sentenceω.Realize, BoundedFormulaω.realize_not] at hn
      exact fun hand => hn hand.1
  · refine ⟨?_, ?_⟩
    · rw [show (τ₁.and τ₂).baseFunctionsIn = ((τ₁.imp τ₂.not).not).baseFunctionsIn from rfl,
        baseFunctionsIn_not]
      exact baseFunctionsIn_imp_subset hb₁.1 (by rw [baseFunctionsIn_not]; exact hb₂.1)
    · rw [show (τ₁.and τ₂).baseRelationsIn = ((τ₁.imp τ₂.not).not).baseRelationsIn from rfl,
        baseRelationsIn_not]
      exact baseRelationsIn_imp_subset hb₁.2 (by rw [baseRelationsIn_not]; exact hb₂.2)
  · rw [show sentenceJConsts (L' := L) (J := ℕ) (τ₁.and τ₂)
      = sentenceJConsts (L' := L) (J := ℕ) ((τ₁.imp τ₂.not).not) from rfl, sentenceJConsts_not]
    refine sentenceJConsts_imp_subset hc₁ ?_
    rw [sentenceJConsts_not]; exact hc₂
  · intro hq
    replace hq : hasQuantSigned true (τ₁.and τ₂) := hq
    rw [hasQuantSigned_and] at hq
    exact hq.elim hu₁ hu₂
  · intro hq
    replace hq : hasQuantSigned false (τ₁.and τ₂) := hq
    rw [hasQuantSigned_and] at hq
    exact hq.elim hx₁ hx₂

/-! ## The fresh-witness rules

The payoff of labelling.  A witness constant `c` fresh for **both** sides is added to **one** of them.
Freshness on the *opposite* side is what forbids the separator from mentioning `c` — via the
shared-constant condition — so the separator transports **unchanged**; freshness on the *own* side is
what moves the entailment.  No constant abstraction appears anywhere. -/

/-- Entailment transfer for a separator that does not mention the witness constant, from an
existential parent.  The `_of_fresh` suffix distinguishes these from the quarantined
constant-*free* versions in `FefermanProjection.lean`: here the separator need only avoid the single
witness constant, which is exactly what the shared-constant condition delivers. -/
theorem entails_of_entails_insert_witness_of_fresh (c : ℕ) (φc τ : L[[ℕ]].Sentenceω)
    (hpar : genEx c φc ∈ T) (hcT : ∀ γ ∈ T, c ∉ sentenceJConsts (L' := L) (J := ℕ) γ)
    (hcτ : c ∉ sentenceJConsts (L' := L) (J := ℕ) τ)
    (h : Theoryω.Entails (insert φc T) τ) : Theoryω.Entails T τ := by
  intro N instN neN hmodel
  set base := (L.lhomWithConstants ℕ).reduct N with hbase
  set hm := ambientConstMap (L := L) N with hh
  have bridge : ∀ (ρ : L[[ℕ]].Sentenceω),
      @Sentenceω.Realize L[[ℕ]] ρ N instN
        ↔ @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 0 ρ Empty.elim Fin.elim0 :=
    fun ρ => ambient_realize_iff_wc (S := instN) ρ Empty.elim Fin.elim0
  have hφ : @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 0 (genEx c φc)
      Empty.elim Fin.elim0 := (bridge _).mp (hmodel _ hpar)
  obtain ⟨x, hx⟩ := (realize_genEx base hm c φc).mp hφ
  have hT : ∀ γ ∈ T,
      @BoundedFormulaω.Realize L[[ℕ]] N (wc base (Function.update hm c x)) Empty 0 γ
        Empty.elim Fin.elim0 := by
    intro γ hγ
    have hg : @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 0 γ Empty.elim Fin.elim0 :=
      (bridge _).mp (hmodel _ hγ)
    have hcongr : ∀ k ∈ sentenceJConsts (L' := L) (J := ℕ) γ, hm k = Function.update hm c x k := by
      intro k hk
      have hkc : (k : ℕ) ≠ c := fun heq => hcT γ hγ (heq ▸ hk)
      exact (Function.update_of_ne (α := ℕ) hkc x hm).symm
    rwa [BoundedFormulaω.realize_congr_const base γ hcongr Empty.elim Fin.elim0] at hg
  have hτ : @BoundedFormulaω.Realize L[[ℕ]] N (wc base (Function.update hm c x)) Empty 0 τ
      Empty.elim Fin.elim0 :=
    @h N (wc base (Function.update hm c x)) neN (fun ρ hρ => by
      rcases Set.mem_insert_iff.mp hρ with rfl | hρ
      · exact hx
      · exact hT ρ hρ)
  have hback : ∀ k ∈ sentenceJConsts (L' := L) (J := ℕ) τ, Function.update hm c x k = hm k := by
    intro k hk
    have hkc : (k : ℕ) ≠ c := fun heq => hcτ (heq ▸ hk)
    exact Function.update_of_ne (α := ℕ) hkc x hm
  exact (bridge _).mpr
    ((BoundedFormulaω.realize_congr_const base τ hback Empty.elim Fin.elim0).mp hτ)

/-- The kernel's `neg_all_witness` shape: parent `(φ.all).not`, inserted witness
`(instConst c φ).not`. -/
theorem entails_of_entails_insert_negInstConst_of_fresh (c : ℕ) (φ : L[[ℕ]].BoundedFormulaω Empty 1)
    (τ : L[[ℕ]].Sentenceω) (hpar : (BoundedFormulaω.all φ).not ∈ T)
    (hcT : ∀ γ ∈ T, c ∉ sentenceJConsts (L' := L) (J := ℕ) γ)
    (hcτ : c ∉ sentenceJConsts (L' := L) (J := ℕ) τ)
    (h : Theoryω.Entails (insert ((instConst c φ).not) T) τ) : Theoryω.Entails T τ := by
  have hcφ : c ∉ sentenceJConsts (L' := L) (J := ℕ) φ := by
    have := hcT _ hpar
    rwa [sentenceJConsts_not, sentenceJConsts_all] at this
  intro N instN neN hmodel
  set base := (L.lhomWithConstants ℕ).reduct N with hbase
  set hm := ambientConstMap (L := L) N with hh
  have bridge : ∀ (ρ : L[[ℕ]].Sentenceω),
      @Sentenceω.Realize L[[ℕ]] ρ N instN
        ↔ @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 0 ρ Empty.elim Fin.elim0 :=
    fun ρ => ambient_realize_iff_wc (S := instN) ρ Empty.elim Fin.elim0
  have hnall : ¬ ∀ x : N, @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 1 φ Empty.elim
      (Fin.snoc Fin.elim0 x) := (bridge _).mp (hmodel _ hpar)
  obtain ⟨x, hx⟩ := not_forall.mp hnall
  have hsnoc : (Fin.snoc Fin.elim0 x : Fin 1 → N) = (fun _ => x) := by
    funext i; simp [Fin.snoc, Fin.eq_zero i]
  rw [hsnoc] at hx
  have hT : ∀ γ ∈ T,
      @BoundedFormulaω.Realize L[[ℕ]] N (wc base (Function.update hm c x)) Empty 0 γ
        Empty.elim Fin.elim0 := by
    intro γ hγ
    have hg : @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 0 γ Empty.elim Fin.elim0 :=
      (bridge _).mp (hmodel _ hγ)
    have hcongr : ∀ k ∈ sentenceJConsts (L' := L) (J := ℕ) γ, hm k = Function.update hm c x k := by
      intro k hk
      have hkc : (k : ℕ) ≠ c := fun heq => hcT γ hγ (heq ▸ hk)
      exact (Function.update_of_ne (α := ℕ) hkc x hm).symm
    rwa [BoundedFormulaω.realize_congr_const base γ hcongr Empty.elim Fin.elim0] at hg
  have hwit : @BoundedFormulaω.Realize L[[ℕ]] N (wc base (Function.update hm c x)) Empty 0
      ((instConst c φ).not) Empty.elim Fin.elim0 := by
    intro hcontra
    have h1 := (realize_instConst base (Function.update hm c x) c φ).mp hcontra
    rw [show (fun _ : Fin 1 => Function.update hm c x c) = (fun _ : Fin 1 => x) from
      funext fun _ => Function.update_self c x hm] at h1
    have hcongr : ∀ k ∈ sentenceJConsts (L' := L) (J := ℕ) φ,
        Function.update hm c x k = hm k := by
      intro k hk
      have hkc : (k : ℕ) ≠ c := fun heq => hcφ (heq ▸ hk)
      exact Function.update_of_ne (α := ℕ) hkc x hm
    exact hx ((BoundedFormulaω.realize_congr_const base φ hcongr Empty.elim (fun _ => x)).mp h1)
  have hτ : @BoundedFormulaω.Realize L[[ℕ]] N (wc base (Function.update hm c x)) Empty 0 τ
      Empty.elim Fin.elim0 :=
    @h N (wc base (Function.update hm c x)) neN (fun ρ hρ => by
      rcases Set.mem_insert_iff.mp hρ with rfl | hρ
      · exact hwit
      · exact hT ρ hρ)
  have hback : ∀ k ∈ sentenceJConsts (L' := L) (J := ℕ) τ, Function.update hm c x k = hm k := by
    intro k hk
    have hkc : (k : ℕ) ≠ c := fun heq => hcτ (heq ▸ hk)
    exact Function.update_of_ne (α := ℕ) hkc x hm
  exact (bridge _).mpr
    ((BoundedFormulaω.realize_congr_const base τ hback Empty.elim Fin.elim0).mp hτ)

/-- **Fresh witness on the left.**  The separator is transported unchanged: opposite-side freshness
plus the shared-constant condition force `c ∉ sentenceJConsts θ`. -/
theorem budgetedPairInsep_witness_left (c : ℕ) (φ : L[[ℕ]].BoundedFormulaω Empty 1)
    (hpar : (BoundedFormulaω.all φ).not ∈ Γ)
    (hcΓ : c ∉ theoryJConsts (L := L) Γ) (hcΔ : c ∉ theoryJConsts (L := L) Δ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ (insert ((instConst c φ).not) Γ) Δ := by
  rintro ⟨θ, hE, hN, hb, hc, hu, hx⟩
  have hcθ : c ∉ sentenceJConsts (L' := L) (J := ℕ) θ := fun hk => hcΔ (hc hk).2
  -- the left support and budget do not grow past what the parent already licenses
  have hcΓ' : theoryJConsts (L := L) (insert ((instConst c φ).not) Γ)
      ⊆ insert c (theoryJConsts Γ) := by
    rw [theoryJConsts_insert, sentenceJConsts_not]
    refine Set.union_subset (fun k hk => ?_) (Set.subset_insert _ _)
    rcases sentenceJConsts_instConst_subset c φ hk with hk | hk
    · exact Set.mem_insert_of_mem _ ((sentenceJConsts_subset_theoryJConsts hpar)
        (by rwa [sentenceJConsts_not]))
    · exact Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hk))
  have huΓ' : Theoryω.HasQuantSigned true (insert ((instConst c φ).not) Γ)
      → Theoryω.HasQuantSigned true Γ := by
    intro hq
    rcases Theoryω.hasQuantSigned_insert.mp hq with hq | hq
    · refine Theoryω.hasQuantSigned_of_mem hpar ?_
      rw [hasQuantSigned_not, hasQuantSigned_all]
      refine Or.inr ?_
      rw [hasQuantSigned_not] at hq
      rw [show (instConst c φ) = (φ.openBounds).subst (fun _ => constTerm c) from rfl,
        hasQuantSigned_subst] at hq
      rwa [hasQuantSigned_openBounds] at hq
    · exact hq
  refine h ⟨θ, ?_, hN, hb, ?_, fun hq => huΓ' (hu hq), hx⟩
  · exact entails_of_entails_insert_negInstConst_of_fresh c φ θ hpar
      (notMem_theoryJConsts_iff.mp hcΓ) hcθ hE
  · refine Set.subset_inter (fun k hk => ?_) (fun k hk => (hc hk).2)
    rcases hcΓ' (hc hk).1 with hk' | hk'
    · exact absurd (hk' ▸ hk) hcθ
    · exact hk'

/-- **Fresh witness on the right**, the mirror image. -/
theorem budgetedPairInsep_witness_right (c : ℕ) (φ : L[[ℕ]].BoundedFormulaω Empty 1)
    (hpar : (BoundedFormulaω.all φ).not ∈ Δ)
    (hcΓ : c ∉ theoryJConsts (L := L) Γ) (hcΔ : c ∉ theoryJConsts (L := L) Δ)
    (h : BudgetedPairInsep F₁ R₁ F₂ R₂ Γ Δ) :
    BudgetedPairInsep F₁ R₁ F₂ R₂ Γ (insert ((instConst c φ).not) Δ) := by
  rintro ⟨θ, hE, hN, hb, hc, hu, hx⟩
  have hcθ : c ∉ sentenceJConsts (L' := L) (J := ℕ) θ := fun hk => hcΓ (hc hk).1
  have hcΔ' : theoryJConsts (L := L) (insert ((instConst c φ).not) Δ)
      ⊆ insert c (theoryJConsts Δ) := by
    rw [theoryJConsts_insert, sentenceJConsts_not]
    refine Set.union_subset (fun k hk => ?_) (Set.subset_insert _ _)
    rcases sentenceJConsts_instConst_subset c φ hk with hk | hk
    · exact Set.mem_insert_of_mem _ ((sentenceJConsts_subset_theoryJConsts hpar)
        (by rwa [sentenceJConsts_not]))
    · exact Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hk))
  have huΔ' : Theoryω.HasQuantSigned true (insert ((instConst c φ).not) Δ)
      → Theoryω.HasQuantSigned true Δ := by
    intro hq
    rcases Theoryω.hasQuantSigned_insert.mp hq with hq | hq
    · refine Theoryω.hasQuantSigned_of_mem hpar ?_
      rw [hasQuantSigned_not, hasQuantSigned_all]
      refine Or.inr ?_
      rw [hasQuantSigned_not] at hq
      rw [show (instConst c φ) = (φ.openBounds).subst (fun _ => constTerm c) from rfl,
        hasQuantSigned_subst] at hq
      rwa [hasQuantSigned_openBounds] at hq
    · exact hq
  refine h ⟨θ, hE, ?_, hb, ?_, hu, fun hq => huΔ' (hx hq)⟩
  · exact entails_of_entails_insert_negInstConst_of_fresh c φ θ.not hpar
      (notMem_theoryJConsts_iff.mp hcΔ) (by rwa [sentenceJConsts_not]) hN
  · refine Set.subset_inter (fun k hk => (hc hk).1) (fun k hk => ?_)
    rcases hcΔ' (hc hk).2 with hk' | hk'
    · exact absurd (hk' ▸ hk) hcθ
    · exact hk'

/-! ## The root collapse and the interpolant equation -/

/-- **Root collapse.**  A budgeted separator against a right side with no universal occurrence is
universal; against constant-free sides it is constant-free. -/
theorem isUniversal_of_budgetedPairSeparates {θ : L[[ℕ]].Sentenceω}
    (h : BudgetedPairSeparates F₁ R₁ F₂ R₂ Γ Δ θ) (hΔ : ¬ Theoryω.HasQuantSigned true Δ) :
    IsUniversal θ :=
  (isUniversal_iff_not_hasExistential θ).mpr fun hq => hΔ (h.2.2.2.2.2 hq)

theorem sentenceJConsts_eq_empty_of_budgetedPairSeparates {θ : L[[ℕ]].Sentenceω}
    (h : BudgetedPairSeparates F₁ R₁ F₂ R₂ Γ Δ θ) (hΓ : theoryJConsts (L := L) Γ = ∅) :
    sentenceJConsts (L' := L) (J := ℕ) θ = ∅ := by
  refine Set.subset_empty_iff.mp fun k hk => ?_
  rw [← hΓ]
  exact (h.2.2.2.1 hk).1

/-- **The root equation.**  Failure of the invariant at the root pair `({r₁}, {r₂.not})` — with `r₂`
carrying no existential occurrence, i.e. universal, and the roots constant-free — delivers exactly a
Malitz interpolant: universal, shared-vocabulary, constant-free, `r₁ ⊨ θ` and `θ ⊨ r₂`. -/
theorem exists_universal_interpolant_of_not_budgetedPairInsep {r₁ r₂ : L[[ℕ]].Sentenceω}
    (hr₂ : ¬ hasQuantSigned false r₂) (hc₁ : sentenceJConsts (L' := L) (J := ℕ) r₁ = ∅)
    (h : ¬ BudgetedPairInsep F₁ R₁ F₂ R₂ {r₁} {r₂.not}) :
    ∃ θ : L[[ℕ]].Sentenceω, IsUniversal θ ∧ θ ∈ SentBnd (F₁ ∩ F₂) (R₁ ∩ R₂) ∧
      sentenceJConsts (L' := L) (J := ℕ) θ = ∅ ∧
      Sentenceω.Entails r₁ θ ∧ Sentenceω.Entails θ r₂ := by
  simp only [BudgetedPairInsep, not_not] at h
  obtain ⟨θ, hsep⟩ := h
  have hΔ : ¬ Theoryω.HasQuantSigned true ({r₂.not} : Set L[[ℕ]].Sentenceω) := by
    rintro ⟨ρ, hρ, hq⟩
    rw [Set.mem_singleton_iff] at hρ
    subst hρ
    exact hr₂ ((hasQuantSigned_not true r₂).mp hq)
  have hΓ : theoryJConsts (L := L) ({r₁} : Set L[[ℕ]].Sentenceω) = ∅ := by
    refine Set.subset_empty_iff.mp fun k hk => ?_
    simp only [theoryJConsts, Set.mem_iUnion, Set.mem_singleton_iff] at hk
    obtain ⟨ρ, rfl, hk⟩ := hk
    rw [hc₁] at hk
    exact hk
  refine ⟨θ, isUniversal_of_budgetedPairSeparates hsep hΔ, hsep.2.2.1,
    sentenceJConsts_eq_empty_of_budgetedPairSeparates hsep hΓ, hsep.1, ?_⟩
  intro N instN neN hmodel
  by_contra hnr₂
  have := @hsep.2.1 N instN neN (fun ρ hρ => by
    rw [Set.mem_singleton_iff] at hρ
    subst hρ
    rw [Sentenceω.Realize, BoundedFormulaω.realize_not]
    exact hnr₂)
  rw [Sentenceω.Realize, BoundedFormulaω.realize_not] at this
  exact this (hmodel _ rfl)

end FirstOrder.Language
