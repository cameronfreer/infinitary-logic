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

end FirstOrder.Language
