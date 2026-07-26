/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.Interpolation.PairedInsepFamily
import InfinitaryLogic.Lomega1omega.QuantifierClass

/-!
# The canonical side projections and the constant-free separator (issue #15, Unit 3, steps 1–3)

The certificate frozen in `docs/malitz-source-reconstruction.md` §6 and `docs/malitz-audit.md` §D8,
reconstructed from Feferman's many-sorted interpolation theorem as presented in Väänänen,
*Interpolation in model theory* (arXiv 2507.19097), Theorem 22.

Two things distinguish it from the Unit-2 attempt (`MalitzC7Spike.lean`), and both are load-bearing.

**One set, not a pair.**  Väänänen's `S₁`, `S₂` are the **canonical side-language projections** of a
single finite set `S`, so a *shared*-vocabulary sentence lies in **both** of them.  An arbitrary pair
is not a faithful substitute: with `P` shared, the pair `Γ = {P(c)}`, `Δ = {¬P(c)}` has an
inconsistent union yet need admit no constant-free separator, since any separator must mention `c`.
Under the projections both sentences are shared, each projection is inconsistent on its own, and the
constant-free universal `⊥` separates — which is exactly how C0 survives constant-freeness
(`not_fefermanInsep_of_shared_contradiction`).

**No separator support at all**, rather than a budgeted support discharged at the root.  In the
single-sorted Malitz case the existential sort budget is empty, which forbids existential quantifiers
*and* `C*`-constants in the separator at every stage.  The consequence is that the fresh-witness (C7)
step becomes the **identity on the separator**: only the entailment moves, by the reinterpretation
argument, and a constant-free separator is pulled back unchanged
(`entails_of_entails_insert_witness`, `fefermanInsep_insert_witness`).

Because the projections are canonical, the left/right distinction of the paired family **collapses**:
one theorem covers a witness entering either side, or both.

**A deliberate weakening, recorded.**  Feferman's separation relation tracks the *sort* budgets
`Un′`/`Ex′` and permits `C*`-constants in the separator, charged into both.  `FefermanInsep` below
asks only for a **constant-free universal** separator.  That is the **single-sorted,
theorem-oriented specialization** — exactly what Malitz 4.5 needs, since `Ex(ψ) = ∅` for universal
`ψ` collapses the budget to precisely this condition — and it is *not* Feferman's invariant verbatim.
Any many-sorted use (in particular the preservation route, which needs the two-sorted `EXT` encoding)
must reinstate the budgets.
-/

namespace FirstOrder.Language

open FirstOrder Structure BoundedFormulaω

variable {L : Language.{0, 0}} {M : Type}

/-! ## Step 1 — the canonical side projections -/

/-- The **canonical side projection** of `S` to the vocabulary `(F, R)`: the members of `S` whose
base symbols fit inside it.  Constants are not base symbols, so they never obstruct membership, and a
shared sentence lies in the projections of *both* sides. -/
def side (F : Set (Σ n, L.Functions n)) (R : Set (Σ n, L.Relations n))
    (S : Set L[[ℕ]].Sentenceω) : Set L[[ℕ]].Sentenceω := S ∩ SentBnd F R

variable {F F₁ F₂ : Set (Σ n, L.Functions n)} {R R₁ R₂ : Set (Σ n, L.Relations n)}
  {S : Set L[[ℕ]].Sentenceω}

theorem mem_side_iff {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}
    {S : Set L[[ℕ]].Sentenceω} {σ : L[[ℕ]].Sentenceω} :
    σ ∈ side F R S ↔ σ ∈ S ∧ σ ∈ SentBnd F R := Iff.rfl

theorem side_subset {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}
    {S : Set L[[ℕ]].Sentenceω} : side F R S ⊆ S := Set.inter_subset_left

/-- A shared sentence of `S` lies in **both** projections — the overlap the pair representation
loses. -/
theorem mem_side_of_shared {F₁ F₂ : Set (Σ n, L.Functions n)} {R₁ R₂ : Set (Σ n, L.Relations n)}
    {S : Set L[[ℕ]].Sentenceω} {σ : L[[ℕ]].Sentenceω}
    (hmem : σ ∈ S) (hbnd : σ ∈ SentBnd (L := L) (F₁ ∩ F₂) (R₁ ∩ R₂)) :
    σ ∈ side F₁ R₁ S ∧ σ ∈ side F₂ R₂ S :=
  ⟨⟨hmem, hbnd.1.trans Set.inter_subset_left, hbnd.2.trans Set.inter_subset_left⟩,
    ⟨hmem, hbnd.1.trans Set.inter_subset_right, hbnd.2.trans Set.inter_subset_right⟩⟩

theorem side_insert_of_mem {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}
    {S : Set L[[ℕ]].Sentenceω} {σ : L[[ℕ]].Sentenceω} (h : σ ∈ SentBnd F R) :
    side F R (insert σ S) = insert σ (side F R S) := by
  ext ρ
  simp only [side, Set.mem_inter_iff, Set.mem_insert_iff]
  constructor
  · rintro ⟨hρ | hρ, hb⟩
    · exact Or.inl hρ
    · exact Or.inr ⟨hρ, hb⟩
  · rintro (rfl | ⟨hρ, hb⟩)
    · exact ⟨Or.inl rfl, h⟩
    · exact ⟨Or.inr hρ, hb⟩

theorem side_insert_of_notMem {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}
    {S : Set L[[ℕ]].Sentenceω} {σ : L[[ℕ]].Sentenceω} (h : σ ∉ SentBnd F R) :
    side F R (insert σ S) = side F R S := by
  ext ρ
  simp only [side, Set.mem_inter_iff, Set.mem_insert_iff]
  constructor
  · rintro ⟨hρ | hρ, hb⟩
    · exact absurd (hρ ▸ hb) h
    · exact ⟨hρ, hb⟩
  · rintro ⟨hρ, hb⟩
    exact ⟨Or.inr hρ, hb⟩

/-! ## The invariant: no constant-free universal separator of the two projections -/

/-- **(⋆), in the single-sorted Malitz specialization.**  No separator of the two canonical
projections of `S` that is universal, inside the shared vocabulary, and **constant-free**.  There is
no support parameter: the empty existential sort budget forbids `C*`-constants outright. -/
def FefermanInsep (F₁ : Set (Σ n, L.Functions n)) (R₁ : Set (Σ n, L.Relations n))
    (F₂ : Set (Σ n, L.Functions n)) (R₂ : Set (Σ n, L.Relations n))
    (S : Set L[[ℕ]].Sentenceω) : Prop :=
  ¬ ∃ σ : L[[ℕ]].Sentenceω,
    IsUniversal σ ∧ σ ∈ SentBnd (F₁ ∩ F₂) (R₁ ∩ R₂) ∧
    sentenceJConsts (L' := L) (J := ℕ) σ = ∅ ∧
    Theoryω.Entails (side F₁ R₁ S) σ ∧ Theoryω.Entails (side F₂ R₂ S) σ.not

/-! ## The coverage invariant -/

/-- **Coverage**: every member of `S` lies in at least one canonical projection, i.e.
`S = side F₁ R₁ S ∪ side F₂ R₂ S` (the `⊇` half is automatic).  Väänänen's family carries this as
part of membership, and unlike the paired Craig construction it does **not** come for free: it needs
either a joint-language hypothesis on the sentences admitted, or a side-generated universe.

Caveat for the eventual family shell: `GenU` seeds *all* ambient relation atoms, so an ambient symbol
belonging to neither side would break coverage.  The joint `symbSublang` wrapper is what will
discharge it. -/
def Covered (F₁ : Set (Σ n, L.Functions n)) (R₁ : Set (Σ n, L.Relations n))
    (F₂ : Set (Σ n, L.Functions n)) (R₂ : Set (Σ n, L.Relations n))
    (S : Set L[[ℕ]].Sentenceω) : Prop :=
  S ⊆ side F₁ R₁ S ∪ side F₂ R₂ S

theorem covered_iff_eq :
    Covered F₁ R₁ F₂ R₂ S ↔ S = side F₁ R₁ S ∪ side F₂ R₂ S := by
  refine ⟨fun h => Set.Subset.antisymm h ?_, fun h => h.subset⟩
  exact Set.union_subset side_subset side_subset

/-- Coverage is exactly a **joint-language** condition on the sentences admitted: each must fit one of
the two side vocabularies. -/
theorem covered_of_forall_mem_sentBnd
    (h : ∀ σ ∈ S, σ ∈ SentBnd (L := L) F₁ R₁ ∨ σ ∈ SentBnd (L := L) F₂ R₂) :
    Covered F₁ R₁ F₂ R₂ S := by
  intro σ hσ
  rcases h σ hσ with hb | hb
  · exact Or.inl ⟨hσ, hb⟩
  · exact Or.inr ⟨hσ, hb⟩

theorem covered_insert {σ : L[[ℕ]].Sentenceω}
    (hb : σ ∈ SentBnd (L := L) F₁ R₁ ∨ σ ∈ SentBnd (L := L) F₂ R₂)
    (h : Covered F₁ R₁ F₂ R₂ S) : Covered F₁ R₁ F₂ R₂ (insert σ S) := by
  refine covered_of_forall_mem_sentBnd fun ρ hρ => ?_
  rcases Set.mem_insert_iff.mp hρ with rfl | hρ
  · exact hb
  · rcases h hρ with hm | hm
    · exact Or.inl hm.2
    · exact Or.inr hm.2

/-- **A sentence and its negation always lie in exactly the same projections**, because `SentBnd`
membership is negation-invariant.  This is why the two-sided C0 below has only two cases and not
three: the "contradiction split across the two projections" case cannot occur. -/
theorem mem_side_not_iff {σ : L[[ℕ]].Sentenceω} (hmem : σ ∈ S) (hnmem : σ.not ∈ S) :
    σ ∈ side F R S ↔ σ.not ∈ side F R S := by
  simp only [mem_side_iff]
  exact ⟨fun h => ⟨hnmem, sentBnd_not_iff.mpr h.2⟩, fun h => ⟨hmem, sentBnd_not_iff.mp h.2⟩⟩

/-! ## Step 2 — the shared-overlap C0 gate -/

/-- **C0 survives constant-freeness, via the overlap.**  If `S` contains a shared sentence together
with its negation, then `S` is *not* in the family: both lie in the same projection, so that
projection is inconsistent, and the constant-free universal `⊥` separates.

This is precisely the step that fails for an arbitrary pair `(Γ, Δ)` — there the two sentences sit in
different coordinates and no constant-free separator need exist. -/
theorem not_fefermanInsep_of_shared_contradiction {σ : L[[ℕ]].Sentenceω}
    (hmem : σ ∈ S) (hnmem : σ.not ∈ S)
    (hbnd : σ ∈ SentBnd (L := L) (F₁ ∩ F₂) (R₁ ∩ R₂)) :
    ¬ FefermanInsep F₁ R₁ F₂ R₂ S := by
  intro h
  refine h ⟨BoundedFormulaω.falsum, universalSigned_falsum true, ?_, ?_, ?_, ?_⟩
  · exact ⟨by rw [baseFunctionsIn_falsum]; exact Set.empty_subset _,
      by rw [show (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω).baseRelationsIn = ∅ from
        baseRelationsIn_falsum]; exact Set.empty_subset _⟩
  · exact sentenceJConsts_falsum
  -- the first projection contains both `σ` and `σ.not`, hence entails anything
  · intro N instN _ hmodel
    have h1 := hmodel σ (mem_side_of_shared (F₂ := F₂) (R₂ := R₂) hmem hbnd).1
    have h2 := hmodel σ.not
      (mem_side_of_shared (F₂ := F₂) (R₂ := R₂) hnmem (sentBnd_not_iff.mpr hbnd)).1
    rw [Sentenceω.Realize, BoundedFormulaω.realize_not] at h2
    exact absurd h1 h2
  · intro N instN _ _
    rw [Sentenceω.Realize, BoundedFormulaω.realize_not]
    exact fun hf => hf

/-- An inconsistent **first** projection is separated by the constant-free universal `⊥`. -/
theorem not_fefermanInsep_of_left_inconsistent
    (h1 : Theoryω.Entails (side F₁ R₁ S) (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω)) :
    ¬ FefermanInsep F₁ R₁ F₂ R₂ S := by
  intro h
  refine h ⟨BoundedFormulaω.falsum, universalSigned_falsum true, ?_, sentenceJConsts_falsum, h1, ?_⟩
  · exact ⟨by rw [baseFunctionsIn_falsum]; exact Set.empty_subset _,
      by rw [show (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω).baseRelationsIn = ∅ from
        baseRelationsIn_falsum]; exact Set.empty_subset _⟩
  · intro N instN _ _
    rw [Sentenceω.Realize, BoundedFormulaω.realize_not]
    exact fun hf => hf

/-- An inconsistent **second** projection is separated by the constant-free universal `⊤`.  The
two-sided split is what lets C0 be discharged from coverage alone. -/
theorem not_fefermanInsep_of_right_inconsistent
    (h2 : Theoryω.Entails (side F₂ R₂ S) (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω)) :
    ¬ FefermanInsep F₁ R₁ F₂ R₂ S := by
  intro h
  refine h ⟨(BoundedFormulaω.falsum : L[[ℕ]].Sentenceω).not, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isUniversal_not _).mpr (universalSigned_falsum false)
  · refine ⟨?_, ?_⟩
    · rw [baseFunctionsIn_not, baseFunctionsIn_falsum]; exact Set.empty_subset _
    · rw [baseRelationsIn_not,
        show (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω).baseRelationsIn = ∅ from
          baseRelationsIn_falsum]
      exact Set.empty_subset _
  · rw [sentenceJConsts_not]; exact sentenceJConsts_falsum
  · intro N instN _ _
    rw [Sentenceω.Realize, BoundedFormulaω.realize_not]
    exact fun hf => hf
  · intro N instN neN hmodel
    rw [Sentenceω.Realize, BoundedFormulaω.realize_not]
    exact fun _ => @h2 N instN neN hmodel

/-- **C0, in general: `no_contradiction` from coverage alone.**  If `S` contains a sentence together
with its negation then, by coverage, both lie in the *same* projection — `mem_side_not_iff` rules out
a split — and that projection is inconsistent.  The left case is separated by `⊥`, the right by `⊤`.

This supersedes `not_fefermanInsep_of_shared_contradiction`, which handles only the shared case and is
too special to discharge the kernel's `no_contradiction` field. -/
theorem not_fefermanInsep_of_contradiction {σ : L[[ℕ]].Sentenceω}
    (hmem : σ ∈ S) (hnmem : σ.not ∈ S) (hcov : Covered F₁ R₁ F₂ R₂ S) :
    ¬ FefermanInsep F₁ R₁ F₂ R₂ S := by
  have inconsistent : ∀ (F : Set (Σ n, L.Functions n)) (R : Set (Σ n, L.Relations n)),
      σ ∈ side F R S → Theoryω.Entails (side F R S) (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω) := by
    intro F R hσ N instN _ hmodel
    have hp := hmodel σ hσ
    have hn := hmodel σ.not ((mem_side_not_iff hmem hnmem).mp hσ)
    rw [Sentenceω.Realize, BoundedFormulaω.realize_not] at hn
    exact absurd hp hn
  rcases hcov hmem with hσ | hσ
  · exact not_fefermanInsep_of_left_inconsistent (inconsistent _ _ hσ)
  · exact not_fefermanInsep_of_right_inconsistent (inconsistent _ _ hσ)

/-! ## Step 3 — the fresh-witness step is the identity on the separator -/

/-- **The constant-free freshness transfer.**  This is `entails_genEx_of_entails`'s reinterpretation
argument with the conclusion *left alone* instead of existentially generalized: because `σ` mentions
no constants, it is invariant under reinterpreting the fresh `c`, so it can be pulled back unchanged.

The Unit-2 gate had to generalize `σ` (and thereby leave `IsUniversal`); here nothing happens to
`σ`. -/
theorem entails_of_entails_insert_witness (c : ℕ) (φc σ : L[[ℕ]].Sentenceω)
    {T : Set L[[ℕ]].Sentenceω}
    (hpar : genEx c φc ∈ T)
    (hcT : ∀ γ ∈ T, c ∉ sentenceJConsts (L' := L) (J := ℕ) γ)
    (hcσ : sentenceJConsts (L' := L) (J := ℕ) σ = ∅)
    (h : Theoryω.Entails (insert φc T) σ) : Theoryω.Entails T σ := by
  intro N instN neN hmodel
  set base := (L.lhomWithConstants ℕ).reduct N with hbase
  set hm := ambientConstMap (L := L) N with hh
  have bridge : ∀ (ψ : L[[ℕ]].Sentenceω),
      @Sentenceω.Realize L[[ℕ]] ψ N instN
        ↔ @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 0 ψ Empty.elim Fin.elim0 :=
    fun ψ => ambient_realize_iff_wc (S := instN) ψ Empty.elim Fin.elim0
  -- the existential parent supplies the witness
  have hφ : @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 0 (genEx c φc)
      Empty.elim Fin.elim0 := (bridge _).mp (hmodel _ hpar)
  obtain ⟨x, hx⟩ := (realize_genEx base hm c φc).mp hφ
  -- `T` survives the reinterpretation, by freshness
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
  have hσ : @BoundedFormulaω.Realize L[[ℕ]] N (wc base (Function.update hm c x)) Empty 0 σ
      Empty.elim Fin.elim0 :=
    @h N (wc base (Function.update hm c x)) neN (fun ψ hψ => by
      rcases Set.mem_insert_iff.mp hψ with rfl | hψ
      · exact hx
      · exact hT ψ hψ)
  -- `σ` is constant-free, so the reinterpretation is invisible to it
  have hback : ∀ k ∈ sentenceJConsts (L' := L) (J := ℕ) σ, Function.update hm c x k = hm k := by
    intro k hk
    rw [hcσ] at hk
    exact absurd hk (Set.notMem_empty k)
  exact (bridge _).mpr
    ((BoundedFormulaω.realize_congr_const base σ hback Empty.elim Fin.elim0).mp hσ)

/-- **The C7 gate, projection-aware and side-symmetric.**  Adding the witness instance `φc` of an
existential parent `∃x φ` already in `S`, for a constant `c` fresh for `S`, preserves the invariant.
The separator is transported **unchanged**; only the entailments move.

There is no left/right split: because the projections are canonical, `φc` lands in whichever sides
its own symbols allow, and its parent lands in the same ones (`genEx` adds no base symbols), so the
same argument serves each. -/
theorem fefermanInsep_insert_witness (c : ℕ) (φc : L[[ℕ]].Sentenceω)
    (hpar : genEx c φc ∈ S)
    (hcS : ∀ γ ∈ S, c ∉ sentenceJConsts (L' := L) (J := ℕ) γ)
    (h : FefermanInsep F₁ R₁ F₂ R₂ S) :
    FefermanInsep F₁ R₁ F₂ R₂ (insert φc S) := by
  rintro ⟨σ, huniv, hbnd, hcσ, h1, h2⟩
  -- the parent inherits every symbol bound the instance satisfies
  have hparbnd : ∀ (F : Set (Σ n, L.Functions n)) (R : Set (Σ n, L.Relations n)),
      φc ∈ SentBnd F R → genEx c φc ∈ SentBnd F R := by
    intro F R hb
    exact ⟨(baseFunctionsIn_genEx_subset c φc).trans hb.1, by rw [baseRelationsIn_genEx]; exact hb.2⟩
  have hfresh : ∀ (F : Set (Σ n, L.Functions n)) (R : Set (Σ n, L.Relations n)),
      ∀ γ ∈ side F R S, c ∉ sentenceJConsts (L' := L) (J := ℕ) γ :=
    fun _ _ γ hγ => hcS γ (side_subset hγ)
  refine h ⟨σ, huniv, hbnd, hcσ, ?_, ?_⟩
  · by_cases hb : φc ∈ SentBnd F₁ R₁
    · rw [side_insert_of_mem hb] at h1
      exact entails_of_entails_insert_witness c φc σ ⟨hpar, hparbnd _ _ hb⟩ (hfresh _ _) hcσ h1
    · rwa [side_insert_of_notMem hb] at h1
  · by_cases hb : φc ∈ SentBnd F₂ R₂
    · rw [side_insert_of_mem hb] at h2
      refine entails_of_entails_insert_witness c φc σ.not ⟨hpar, hparbnd _ _ hb⟩ (hfresh _ _) ?_ h2
      rw [sentenceJConsts_not]; exact hcσ
    · rwa [side_insert_of_notMem hb] at h2

/-- The other half of why C7 is free: inserting a sentence that each projection it joins already
**entails** cannot create a separator.  This is what makes the `∀`-instantiation step
(`∀x φ ∈ S ⟹ S ∪ {φ(c)}`) cost nothing. -/
theorem fefermanInsep_insert_of_entailed (ψ : L[[ℕ]].Sentenceω)
    (h1 : ψ ∈ SentBnd (L := L) F₁ R₁ → Theoryω.Entails (side F₁ R₁ S) ψ)
    (h2 : ψ ∈ SentBnd (L := L) F₂ R₂ → Theoryω.Entails (side F₂ R₂ S) ψ)
    (h : FefermanInsep F₁ R₁ F₂ R₂ S) :
    FefermanInsep F₁ R₁ F₂ R₂ (insert ψ S) := by
  rintro ⟨σ, huniv, hbnd, hcσ, e1, e2⟩
  refine h ⟨σ, huniv, hbnd, hcσ, ?_, ?_⟩
  · by_cases hb : ψ ∈ SentBnd F₁ R₁
    · rw [side_insert_of_mem hb] at e1
      exact fun N instN neN hmodel =>
        @e1 N instN neN (fun ρ hρ => by
          rcases Set.mem_insert_iff.mp hρ with rfl | hρ
          · exact @h1 hb N instN neN hmodel
          · exact hmodel ρ hρ)
    · rwa [side_insert_of_notMem hb] at e1
  · by_cases hb : ψ ∈ SentBnd F₂ R₂
    · rw [side_insert_of_mem hb] at e2
      exact fun N instN neN hmodel =>
        @e2 N instN neN (fun ρ hρ => by
          rcases Set.mem_insert_iff.mp hρ with rfl | hρ
          · exact @h2 hb N instN neN hmodel
          · exact hmodel ρ hρ)
    · rwa [side_insert_of_notMem hb] at e2


/-! ## The genuine `neg_all_witness` consumer

`fefermanInsep_insert_witness` handles the literal `genEx` shape.  The kernel field
(`ConsistencyPropertyEqOn.neg_all_witness`) instead starts from `(φ.all).not ∈ S` and inserts
`(instConst c φ).not`.  Rather than route through a semantic-congruence step — which would have to
move *projection membership* as well as truth, and `SentBnd` is not invariant under semantic
equivalence — the consumer shape is proved directly.  This is the one place where syntax equivalence,
projection membership, and constant-freeness meet. -/

/-- Constant instantiation does not move the **base relation** symbols (it substitutes a constant,
which is not a base symbol).  The `⊆` half is `baseRelationsIn_instConst_subset`; the equality is what
the projection-membership obligation needs. -/
theorem baseRelationsIn_instConst (c : ℕ) (φ : L[[ℕ]].BoundedFormulaω Empty 1) :
    (instConst c φ).baseRelationsIn = (BoundedFormulaω.all φ).baseRelationsIn := by
  have h1 : (instConst c φ).relationsIn = (BoundedFormulaω.all φ).relationsIn := by
    show ((φ.openBounds).subst _).relationsIn = _
    rw [relationsIn_subst_eq, relationsIn_openBounds_eq]; rfl
  ext s
  simp only [BoundedFormulaω.baseRelationsIn, Set.mem_setOf_eq, h1]

/-- **The consumer-shaped freshness transfer.**  From `(φ.all).not ∈ T` — semantically `∃x ¬φ(x)` —
the witness is produced directly, and the constant-free separator is pulled back unchanged.  No
`genEx`/`instConst` round trip is invoked. -/
theorem entails_of_entails_insert_negInstConst (c : ℕ) (φ : L[[ℕ]].BoundedFormulaω Empty 1)
    (σ : L[[ℕ]].Sentenceω) {T : Set L[[ℕ]].Sentenceω}
    (hpar : (BoundedFormulaω.all φ).not ∈ T)
    (hcT : ∀ γ ∈ T, c ∉ sentenceJConsts (L' := L) (J := ℕ) γ)
    (hcσ : sentenceJConsts (L' := L) (J := ℕ) σ = ∅)
    (h : Theoryω.Entails (insert ((instConst c φ).not) T) σ) : Theoryω.Entails T σ := by
  have hcφ : c ∉ sentenceJConsts (L' := L) (J := ℕ) φ := by
    have := hcT _ hpar
    rwa [sentenceJConsts_not, sentenceJConsts_all] at this
  intro N instN neN hmodel
  set base := (L.lhomWithConstants ℕ).reduct N with hbase
  set hm := ambientConstMap (L := L) N with hh
  have bridge : ∀ (ψ : L[[ℕ]].Sentenceω),
      @Sentenceω.Realize L[[ℕ]] ψ N instN
        ↔ @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 0 ψ Empty.elim Fin.elim0 :=
    fun ψ => ambient_realize_iff_wc (S := instN) ψ Empty.elim Fin.elim0
  -- the negated universal supplies the witness (unfolded, to keep the controlled instance)
  have hnall : ¬ ∀ x : N, @BoundedFormulaω.Realize L[[ℕ]] N (wc base hm) Empty 1 φ Empty.elim
      (Fin.snoc Fin.elim0 x) := (bridge _).mp (hmodel _ hpar)
  obtain ⟨x, hx⟩ := not_forall.mp hnall
  have hsnoc : (Fin.snoc Fin.elim0 x : Fin 1 → N) = (fun _ => x) := by
    funext i; simp [Fin.snoc, Fin.eq_zero i]
  rw [hsnoc] at hx
  -- `T` survives the reinterpretation, by freshness
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
  -- the inserted witness holds after reinterpretation
  have hwit : @BoundedFormulaω.Realize L[[ℕ]] N (wc base (Function.update hm c x)) Empty 0
      ((instConst c φ).not) Empty.elim Fin.elim0 := by
    intro hcon
    have h1 := (realize_instConst base (Function.update hm c x) c φ).mp hcon
    rw [show (fun _ : Fin 1 => Function.update hm c x c) = (fun _ : Fin 1 => x) from
      funext fun _ => Function.update_self c x hm] at h1
    have hcongr : ∀ k ∈ sentenceJConsts (L' := L) (J := ℕ) φ,
        Function.update hm c x k = hm k := by
      intro k hk
      have hkc : (k : ℕ) ≠ c := fun heq => hcφ (heq ▸ hk)
      exact Function.update_of_ne (α := ℕ) hkc x hm
    exact hx ((BoundedFormulaω.realize_congr_const base φ hcongr Empty.elim (fun _ => x)).mp h1)
  have hσ : @BoundedFormulaω.Realize L[[ℕ]] N (wc base (Function.update hm c x)) Empty 0 σ
      Empty.elim Fin.elim0 :=
    @h N (wc base (Function.update hm c x)) neN (fun ψ hψ => by
      rcases Set.mem_insert_iff.mp hψ with rfl | hψ
      · exact hwit
      · exact hT ψ hψ)
  have hback : ∀ k ∈ sentenceJConsts (L' := L) (J := ℕ) σ, Function.update hm c x k = hm k := by
    intro k hk
    rw [hcσ] at hk
    exact absurd hk (Set.notMem_empty k)
  exact (bridge _).mpr
    ((BoundedFormulaω.realize_congr_const base σ hback Empty.elim Fin.elim0).mp hσ)

/-- **The C7 gate in the kernel's `neg_all_witness` shape.**  The two `hb` hypotheses are the
*projection-membership* obligations: whenever the inserted witness joins a side, its negated-universal
parent must join it too.  They are discharged unconditionally in the relational scope
(`fefermanInsep_insert_negInstConst_of_isRelational`), which is #15's frozen scope for interpolation
(§D6); in general they need the reverse inclusion `baseFunctionsIn (all φ) ⊆ baseFunctionsIn
(instConst c φ)`, which the repository currently has only in the `⊆` direction. -/
theorem fefermanInsep_insert_negInstConst (c : ℕ) (φ : L[[ℕ]].BoundedFormulaω Empty 1)
    (hpar : (BoundedFormulaω.all φ).not ∈ S)
    (hcS : ∀ γ ∈ S, c ∉ sentenceJConsts (L' := L) (J := ℕ) γ)
    (hb₁ : (instConst c φ).not ∈ SentBnd F₁ R₁ → (BoundedFormulaω.all φ).not ∈ SentBnd F₁ R₁)
    (hb₂ : (instConst c φ).not ∈ SentBnd F₂ R₂ → (BoundedFormulaω.all φ).not ∈ SentBnd F₂ R₂)
    (h : FefermanInsep F₁ R₁ F₂ R₂ S) :
    FefermanInsep F₁ R₁ F₂ R₂ (insert ((instConst c φ).not) S) := by
  rintro ⟨σ, huniv, hbnd, hcσ, h1, h2⟩
  have hfresh : ∀ (F : Set (Σ n, L.Functions n)) (R : Set (Σ n, L.Relations n)),
      ∀ γ ∈ side F R S, c ∉ sentenceJConsts (L' := L) (J := ℕ) γ :=
    fun _ _ γ hγ => hcS γ (side_subset hγ)
  refine h ⟨σ, huniv, hbnd, hcσ, ?_, ?_⟩
  · by_cases hb : (instConst c φ).not ∈ SentBnd F₁ R₁
    · rw [side_insert_of_mem hb] at h1
      exact entails_of_entails_insert_negInstConst c φ σ ⟨hpar, hb₁ hb⟩ (hfresh _ _) hcσ h1
    · rwa [side_insert_of_notMem hb] at h1
  · by_cases hb : (instConst c φ).not ∈ SentBnd F₂ R₂
    · rw [side_insert_of_mem hb] at h2
      refine entails_of_entails_insert_negInstConst c φ σ.not ⟨hpar, hb₂ hb⟩ (hfresh _ _) ?_ h2
      rw [sentenceJConsts_not]; exact hcσ
    · rwa [side_insert_of_notMem hb] at h2

/-- The relational scope discharges both projection-membership obligations: base function symbols do
not exist, and constant instantiation leaves the base relation symbols equal
(`baseRelationsIn_instConst`). -/
theorem fefermanInsep_insert_negInstConst_of_isRelational [L.IsRelational]
    (c : ℕ) (φ : L[[ℕ]].BoundedFormulaω Empty 1)
    (hpar : (BoundedFormulaω.all φ).not ∈ S)
    (hcS : ∀ γ ∈ S, c ∉ sentenceJConsts (L' := L) (J := ℕ) γ)
    (h : FefermanInsep F₁ R₁ F₂ R₂ S) :
    FefermanInsep F₁ R₁ F₂ R₂ (insert ((instConst c φ).not) S) := by
  have hb : ∀ (F : Set (Σ n, L.Functions n)) (R : Set (Σ n, L.Relations n)),
      (instConst c φ).not ∈ SentBnd F R → (BoundedFormulaω.all φ).not ∈ SentBnd F R := by
    intro F R hmem
    refine ⟨fun t _ => isEmptyElim t.2, ?_⟩
    have := hmem.2
    rwa [baseRelationsIn_not, baseRelationsIn_instConst, ← baseRelationsIn_not] at this
  exact fefermanInsep_insert_negInstConst c φ hpar hcS (hb _ _) (hb _ _) h

end FirstOrder.Language
