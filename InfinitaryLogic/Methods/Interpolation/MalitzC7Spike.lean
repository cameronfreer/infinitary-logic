/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.Interpolation.Inseparability
import InfinitaryLogic.Lomega1omega.QuantifierClass
import InfinitaryLogic.Lomega1omega.Theory

/-!
# The two-sided C7 spike for a universal separator class (issue #15, Unit 2)

The decisive stop/go gate of `docs/malitz-audit.md` §D4.  `MalitzInsepAt` is `InsepAt` with the
separator additionally required to be **universal**; the question is whether the two fresh-witness
(C7) closure steps survive that restriction under candidate 1 —

> `Γ` unrestricted, `Δ` existential, separator universal.

**Right trigger (witness added on the `Δ` side) — clean.**  `genAll`, the `∀`-generalization of a
fresh constant, is introduced here (the project had only `genEx`).  It is *class-preserving*:
`IsUniversal (genAll c σ) ↔ IsUniversal σ`, because `all` is admissible at the universal sign.  With
its two acceptance sequents this gives `malitzInsepAt_witness_of_genAll` with **no side conditions
beyond freshness** — exactly the shape of the existing Craig/Lyndon gates.

**Left trigger (witness added on the `Γ` side) — closes, but not inside the shared vocabulary.**
`genEx` is *not* class-preserving: `genEx c σ` is `∃x σ(x)`, which is `Σ2` for universal `σ`
(`not_isUniversal_genEx` records this separately — it is a fact about `genEx`, not a failure of the
closure).  The replacement argument is the audit's finite-existential-side conjunction: with `Δ`
finite and existential, `δΔ := ⋀ Δ` is existential, so `¬δΔ` is **universal**, `Δ ⊨ ¬¬δΔ` trivially,
and `Γ, ∃x φ(x) ⊨ ¬δΔ` by reinterpreting the fresh constant at the existential witness — freshness
keeps both `Γ` and `Δ` standing, so `σ(c)` and `¬σ(c)` would both hold.

That argument is formalized here as `malitzInsepAt_witness_of_existentialDelta`, and it needs
**three hypotheses about `Δ` that the paired family does not supply**:

```
hΔF : ∀ δ ∈ Δ, δ.baseFunctionsIn ⊆ F
hΔR : ∀ δ ∈ Δ, δ.baseRelationsIn ⊆ R
hΔA : ∀ δ ∈ Δ, sentenceJConsts δ ⊆ ↑A
```

The support bound `hΔA` is benign — `PairedInsepFamilyMem` already carries it.  The two **symbol**
bounds are not: in the interpolation family the separator bound is the *shared* vocabulary
`(F₁ ∩ F₂, R₁ ∩ R₂)` while `Δ ⊆ SentBnd F₂ R₂`, so `¬δΔ` is a legal separator only when
`F₂ ⊆ F₁` and `R₂ ⊆ R₁`.  This is not an artifact of the formalization: a separator built out of
`Δ` itself is exactly what the shared-vocabulary condition forbids, and it is what makes
interpolation a theorem rather than a triviality.

The consequence is recorded in the audit (§D4): the left closure is available **unconditionally for
the relative-preservation theorem** (source Theorem 4.6, whose existential witness carries *no*
symbol condition — instantiate `F`, `R` at the full symbol sets), and is **blocked for the
interpolation theorem** (source Theorem 4.5, which does), so #15 should discharge D7's relative
endpoint before, not after, the interpolation endpoint.
-/

namespace FirstOrder.Language

open FirstOrder Structure BoundedFormulaω

variable {L : Language.{0, 0}} {M : Type}

/-! ## `genAll`: universal generalization of a fresh constant -/

/-- Universally generalize the constant `c_j` out of a sentence: abstract `c_j` into the free
variable `0`, then universally quantify it.  The `∀`-twin of `genEx`. -/
noncomputable def genAll (j : ℕ) (ρ : L[[ℕ]].Sentenceω) : L[[ℕ]].Sentenceω :=
  ((ρ.abstractConst j).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).all

/-- Realizing the universal generalization is realizing the original at every reinterpretation of
`c_j`. -/
theorem realize_genAll (base : L.Structure M) (h : ℕ → M) (j : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 (genAll j ρ) Empty.elim Fin.elim0
      ↔ ∀ x, @BoundedFormulaω.Realize L[[ℕ]] M (wc base (Function.update h j x)) Empty 0 ρ
          Empty.elim Fin.elim0 := by
  letI : L[[ℕ]].Structure M := wc base h
  have hval : ∀ x : M, (Fin.snoc Fin.elim0 x : Fin 1 → M) = (fun _ => x) := by
    intro x; funext i; simp [Fin.snoc, Fin.eq_zero i]
  rw [genAll, BoundedFormulaω.realize_all]
  refine forall_congr' fun x => ?_
  rw [BoundedFormulaω.realize_relabel_sumInr_zero (ρ.abstractConst j) (Fin.snoc Fin.elim0 x),
    hval x]
  exact BoundedFormulaω.realize_abstractConst base h j x ρ Fin.elim0

/-- `c_j` is not in the constant support of its own universal generalization. -/
theorem notMem_sentenceJConsts_genAll (j : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    j ∉ sentenceJConsts (L' := L) (J := ℕ) (genAll j ρ) := by
  rw [genAll]
  intro hmem
  have h2 : sentenceJConsts (L' := L) (J := ℕ)
      (((ρ.abstractConst j).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).all)
      = sentenceJConsts (L' := L) (J := ℕ) (ρ.abstractConst j) := by
    unfold sentenceJConsts
    rw [show ((ρ.abstractConst j).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).all.functionsIn
      = ((ρ.abstractConst j).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).functionsIn from rfl,
      BoundedFormulaω.functionsIn_relabel]
  rw [h2] at hmem
  exact BoundedFormulaω.notMem_sentenceJConsts_abstractConst j ρ hmem

/-! ### Occurrence facts for `genAll` -/

theorem functionsIn_genAll_subset (j : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    (genAll j ρ).functionsIn ⊆ ρ.functionsIn := by
  rw [genAll,
    show (((ρ.abstractConst j).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).all).functionsIn
      = ((ρ.abstractConst j).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).functionsIn from rfl,
    BoundedFormulaω.functionsIn_relabel]
  exact BoundedFormulaω.functionsIn_abstractConst_subset j ρ

theorem baseFunctionsIn_genAll_subset (j : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    (genAll j ρ).baseFunctionsIn ⊆ ρ.baseFunctionsIn :=
  fun _ hs => functionsIn_genAll_subset j ρ hs

theorem relationsIn_genAll (j : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    (genAll j ρ).relationsIn = ρ.relationsIn := by
  rw [genAll,
    show (((ρ.abstractConst j).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).all).relationsIn
      = ((ρ.abstractConst j).relabel (Sum.inr : Fin 1 → Empty ⊕ Fin 1)).relationsIn from rfl,
    BoundedFormulaω.relationsIn_relabel, BoundedFormulaω.relationsIn_abstractConst]

theorem baseRelationsIn_genAll (j : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    (genAll j ρ).baseRelationsIn = ρ.baseRelationsIn := by
  unfold BoundedFormulaω.baseRelationsIn
  rw [relationsIn_genAll]

theorem sentenceJConsts_genAll_subset (j : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    sentenceJConsts (L' := L) (J := ℕ) (genAll j ρ) ⊆ sentenceJConsts (L' := L) (J := ℕ) ρ :=
  fun _ hs => functionsIn_genAll_subset j ρ hs

/-! ### The quantifier class of `genAll` (and the `genEx` non-fact) -/

/-- Constant abstraction does not move the quantifier class. -/
theorem BoundedFormulaω.universalSigned_abstractConst (j : ℕ) (s : Bool) :
    ∀ {n : ℕ} (φ : L[[ℕ]].BoundedFormulaω Empty n),
      universalSigned s (φ.abstractConst j) ↔ universalSigned s φ := by
  intro n φ
  induction φ generalizing s with
  | falsum => exact Iff.rfl
  | equal t u => exact Iff.rfl
  | rel R ts => exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    show universalSigned (!s) (φ.abstractConst j) ∧ universalSigned s (ψ.abstractConst j) ↔ _
    exact and_congr (ihφ (!s)) (ihψ s)
  | all φ ih =>
    show s = true ∧ universalSigned s (φ.abstractConst j) ↔ _
    exact and_congr_right fun _ => ih s
  | iSup φs ih =>
    show (∀ i, universalSigned s ((φs i).abstractConst j)) ↔ _
    exact forall_congr' fun i => ih i s
  | iInf φs ih =>
    show (∀ i, universalSigned s ((φs i).abstractConst j)) ↔ _
    exact forall_congr' fun i => ih i s

/-- **`genAll` is class-preserving**: universally generalizing a fresh constant out of a universal
sentence leaves it universal.  This is the whole point of the right-hand C7 trigger. -/
theorem isUniversal_genAll (j : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    IsUniversal (genAll j ρ) ↔ IsUniversal ρ := by
  rw [genAll]
  show (true = true ∧ universalSigned true _) ↔ _
  rw [BoundedFormulaω.universalSigned_relabel, BoundedFormulaω.universalSigned_abstractConst]
  exact and_iff_right rfl

/-- **`genEx` is not class-preserving**, recorded separately: `genEx j ρ` is never universal, since
it is a negatively-occurring `all`.  This is a fact about the *construction*, and is not by itself a
failure of the left closure (see `malitzInsepAt_witness_of_existentialDelta`). -/
theorem not_isUniversal_genEx (j : ℕ) (ρ : L[[ℕ]].Sentenceω) :
    ¬ IsUniversal (genEx j ρ) :=
  not_isUniversal_ex _

/-! ### The `genAll` acceptance sequents -/

variable {j : ℕ} {φc σc : L[[ℕ]].Sentenceω} {Γ Δ : Set L[[ℕ]].Sentenceω}

/-- **Acceptance, `Γ` side**: `Γ ⊨ σ(c)` upgrades to `Γ ⊨ ∀x σ(x)` when `c_j` is fresh for `Γ`.
Unlike `genEx`'s `Γ`-side sequent this genuinely needs freshness — `∀`-introduction is not
weakening. -/
theorem entails_genAll_of_entails
    (hfresh : ∀ γ ∈ Γ, j ∉ sentenceJConsts (L' := L) (J := ℕ) γ)
    (hyp : Theoryω.Entails Γ σc) : Theoryω.Entails Γ (genAll j σc) := by
  intro M instM neM hmodel
  set base := (L.lhomWithConstants ℕ).reduct M with hbase
  set h := ambientConstMap (L := L) M with hh
  have bridge : ∀ (ψ : L[[ℕ]].Sentenceω),
      @Sentenceω.Realize L[[ℕ]] ψ M instM
        ↔ @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 ψ Empty.elim Fin.elim0 :=
    fun ψ => ambient_realize_iff_wc (S := instM) ψ Empty.elim Fin.elim0
  refine (bridge _).mpr ((realize_genAll base h j σc).mpr fun x => ?_)
  have hΓ : ∀ γ ∈ Γ,
      @BoundedFormulaω.Realize L[[ℕ]] M (wc base (Function.update h j x)) Empty 0 γ
        Empty.elim Fin.elim0 := by
    intro γ hγ
    have hg : @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 γ Empty.elim Fin.elim0 :=
      (bridge _).mp (hmodel _ hγ)
    have hcongr : ∀ k ∈ sentenceJConsts (L' := L) (J := ℕ) γ, h k = Function.update h j x k := by
      intro k hk
      have hkj : (k : ℕ) ≠ j := fun heq => hfresh γ hγ (heq ▸ hk)
      exact (Function.update_of_ne (α := ℕ) hkj x h).symm
    rwa [BoundedFormulaω.realize_congr_const base γ hcongr Empty.elim Fin.elim0] at hg
  exact @hyp M (wc base (Function.update h j x)) neM hΓ

/-- **Acceptance, `Δ` side**: `Δ, δ(c) ⊨ ¬σ(c)` upgrades to `Δ, ∃x δ(x) ⊨ ¬∀x σ(x)` when `c_j` is
fresh for `Δ`.  The witness for `∃x δ(x)` is exactly the reinterpretation that refutes `∀x σ(x)`. -/
theorem entails_not_genAll_of_entails_not
    (hfresh : ∀ δ ∈ Δ, j ∉ sentenceJConsts (L' := L) (J := ℕ) δ)
    (hyp : Theoryω.Entails (insert φc Δ) σc.not) :
    Theoryω.Entails (insert (genEx j φc) Δ) (genAll j σc).not := by
  intro M instM neM hmodel
  set base := (L.lhomWithConstants ℕ).reduct M with hbase
  set h := ambientConstMap (L := L) M with hh
  have bridge : ∀ (ψ : L[[ℕ]].Sentenceω),
      @Sentenceω.Realize L[[ℕ]] ψ M instM
        ↔ @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 ψ Empty.elim Fin.elim0 :=
    fun ψ => ambient_realize_iff_wc (S := instM) ψ Empty.elim Fin.elim0
  show @Sentenceω.Realize L[[ℕ]] (genAll j σc).not M instM
  rw [Sentenceω.Realize, BoundedFormulaω.realize_not]
  intro hcon
  have hcon' : @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 (genAll j σc)
      Empty.elim Fin.elim0 := (bridge _).mp hcon
  have hφ : @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 (genEx j φc) Empty.elim Fin.elim0 :=
    (bridge _).mp (hmodel _ (Set.mem_insert _ _))
  obtain ⟨x, hx⟩ := (realize_genEx base h j φc).mp hφ
  have hΔ : ∀ δ ∈ Δ,
      @BoundedFormulaω.Realize L[[ℕ]] M (wc base (Function.update h j x)) Empty 0 δ
        Empty.elim Fin.elim0 := by
    intro δ hδ
    have hg : @BoundedFormulaω.Realize L[[ℕ]] M (wc base h) Empty 0 δ Empty.elim Fin.elim0 :=
      (bridge _).mp (hmodel _ (Set.mem_insert_of_mem _ hδ))
    have hcongr : ∀ k ∈ sentenceJConsts (L' := L) (J := ℕ) δ, h k = Function.update h j x k := by
      intro k hk
      have hkj : (k : ℕ) ≠ j := fun heq => hfresh δ hδ (heq ▸ hk)
      exact (Function.update_of_ne (α := ℕ) hkj x h).symm
    rwa [BoundedFormulaω.realize_congr_const base δ hcongr Empty.elim Fin.elim0] at hg
  have hnot : @BoundedFormulaω.Realize L[[ℕ]] M (wc base (Function.update h j x)) Empty 0 σc.not
      Empty.elim Fin.elim0 :=
    @hyp M (wc base (Function.update h j x)) neM (fun ψ hψ => by
      rcases Set.mem_insert_iff.mp hψ with rfl | hψ
      · exact hx
      · exact hΔ ψ hψ)
  exact hnot ((realize_genAll base h j σc).mp hcon' x)

/-! ## The universal-separator inseparability predicate -/

/-- `InsepAt` with the separator additionally required to be **universal** (candidate 1 of the
audit's §D4). -/
def MalitzInsepAt (F : Set (Σ n, L.Functions n)) (R : Set (Σ n, L.Relations n))
    (A : Finset ℕ) (Γ Δ : Set L[[ℕ]].Sentenceω) : Prop :=
  ¬ ∃ σ : L[[ℕ]].Sentenceω,
    IsUniversal σ ∧
    σ.baseFunctionsIn ⊆ F ∧ σ.baseRelationsIn ⊆ R ∧
    sentenceJConsts (L' := L) (J := ℕ) σ ⊆ (↑A : Set ℕ) ∧
    Theoryω.Entails Γ σ ∧ Theoryω.Entails Δ σ.not

variable {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)} {A : Finset ℕ}

/-- **Gate 2 — the right trigger.**  A universal separator of the pair with the witness added on
the `Δ` side abstracts, by `genAll`, to a universal separator of the existential pair.  No side
conditions beyond freshness: this is the clean half of the spike. -/
theorem malitzInsepAt_witness_of_genAll (c : ℕ) (φc : L[[ℕ]].Sentenceω)
    (hcΓ : ∀ γ ∈ Γ, c ∉ sentenceJConsts (L' := L) (J := ℕ) γ)
    (hcΔ : ∀ δ ∈ Δ, c ∉ sentenceJConsts (L' := L) (J := ℕ) δ)
    (h : MalitzInsepAt F R A Γ (insert (genEx c φc) Δ)) :
    MalitzInsepAt F R (insert c A) Γ (insert φc Δ) := by
  rintro ⟨σ, huniv, hbf, hbr, hsupp, hΓσ, hΔσ⟩
  refine h ⟨genAll c σ, (isUniversal_genAll c σ).mpr huniv,
    (baseFunctionsIn_genAll_subset c σ).trans hbf, ?_, ?_, ?_, ?_⟩
  · rw [baseRelationsIn_genAll]; exact hbr
  · intro k hk
    have hk1 : k ∈ sentenceJConsts (L' := L) (J := ℕ) σ := sentenceJConsts_genAll_subset c σ hk
    have hk2 : k ≠ c := fun heq => notMem_sentenceJConsts_genAll c σ (heq ▸ hk)
    have hmem := hsupp hk1
    simp only [Finset.coe_insert, Set.mem_insert_iff] at hmem
    exact hmem.resolve_left hk2
  · exact entails_genAll_of_entails hcΓ hΓσ
  · exact entails_not_genAll_of_entails_not hcΔ hΔσ

/-! ## The left trigger: the finite existential side conjunction -/

section Conjunction

variable {T : L[[ℕ]].Theoryω} {hT : T.Countable}

/-- A countable conjunction of existential sentences is existential. -/
theorem isExistential_conjunction (T : L[[ℕ]].Theoryω) (hT : T.Countable)
    (h : ∀ σ ∈ T, IsExistential σ) : IsExistential (T.conjunction hT) := by
  classical
  rw [Theoryω.conjunction]
  split_ifs with hne
  · refine fun n => h _ ?_
    exact (hT.exists_eq_range hne).choose_spec.symm.subset (Set.mem_range_self n)
  · exact ⟨trivial, trivial⟩

theorem baseFunctionsIn_conjunction_subset (T : L[[ℕ]].Theoryω) (hT : T.Countable)
    (h : ∀ σ ∈ T, σ.baseFunctionsIn ⊆ F) : (T.conjunction hT).baseFunctionsIn ⊆ F := by
  classical
  rw [Theoryω.conjunction]
  split_ifs with hne
  · intro s hs
    simp only [BoundedFormulaω.baseFunctionsIn, BoundedFormulaω.functionsIn, Set.mem_setOf_eq,
      Set.mem_iUnion] at hs
    obtain ⟨n, hn⟩ := hs
    exact h _ ((hT.exists_eq_range hne).choose_spec.symm.subset (Set.mem_range_self n)) hn
  · intro s hs
    simp only [BoundedFormulaω.baseFunctionsIn, BoundedFormulaω.functionsIn, Set.mem_setOf_eq,
      Set.union_self, Set.mem_empty_iff_false] at hs

theorem baseRelationsIn_conjunction_subset (T : L[[ℕ]].Theoryω) (hT : T.Countable)
    (h : ∀ σ ∈ T, σ.baseRelationsIn ⊆ R) : (T.conjunction hT).baseRelationsIn ⊆ R := by
  classical
  rw [Theoryω.conjunction]
  split_ifs with hne
  · intro s hs
    simp only [BoundedFormulaω.baseRelationsIn, BoundedFormulaω.relationsIn, Set.mem_setOf_eq,
      Set.mem_iUnion] at hs
    obtain ⟨n, hn⟩ := hs
    exact h _ ((hT.exists_eq_range hne).choose_spec.symm.subset (Set.mem_range_self n)) hn
  · intro s hs
    simp only [BoundedFormulaω.baseRelationsIn, BoundedFormulaω.relationsIn, Set.mem_setOf_eq,
      Set.union_self, Set.mem_empty_iff_false] at hs

theorem sentenceJConsts_conjunction_subset (T : L[[ℕ]].Theoryω) (hT : T.Countable) {A : Set ℕ}
    (h : ∀ σ ∈ T, sentenceJConsts (L' := L) (J := ℕ) σ ⊆ A) :
    sentenceJConsts (L' := L) (J := ℕ) (T.conjunction hT) ⊆ A := by
  classical
  rw [Theoryω.conjunction]
  split_ifs with hne
  · intro k hk
    simp only [sentenceJConsts, BoundedFormulaω.functionsIn, Set.mem_setOf_eq,
      Set.mem_iUnion] at hk
    obtain ⟨n, hn⟩ := hk
    exact h _ ((hT.exists_eq_range hne).choose_spec.symm.subset (Set.mem_range_self n)) hn
  · intro k hk
    simp only [sentenceJConsts, BoundedFormulaω.functionsIn, Set.mem_setOf_eq, Set.union_self,
      Set.mem_empty_iff_false] at hk

end Conjunction

/-- **Gate 1 — the left trigger**, by the audit's finite-existential-side conjunction.  A universal
separator of the pair with the witness added on the `Γ` side yields the universal separator `¬⋀Δ`
of the existential pair.  `genEx` is deliberately *not* used: it is not class-preserving
(`not_isUniversal_genEx`).

The three `Δ`-bounds are the price.  `hΔA` is free in the paired family; `hΔF`/`hΔR` are **not** —
they say `Δ` already lies inside the separator's symbol budget, which for the interpolation family
(`F = F₁ ∩ F₂`, `Δ ⊆ SentBnd F₂ R₂`) means `F₂ ⊆ F₁` and `R₂ ⊆ R₁`.  For the relative-preservation
endpoint, where the witness sentence carries no symbol condition, they are discharged by taking
`F`, `R` to be everything. -/
theorem malitzInsepAt_witness_of_existentialDelta (c : ℕ) (φc : L[[ℕ]].Sentenceω)
    (hΔc : Δ.Countable) (hΔex : ∀ δ ∈ Δ, IsExistential δ)
    (hΔF : ∀ δ ∈ Δ, δ.baseFunctionsIn ⊆ F) (hΔR : ∀ δ ∈ Δ, δ.baseRelationsIn ⊆ R)
    (hΔA : ∀ δ ∈ Δ, sentenceJConsts (L' := L) (J := ℕ) δ ⊆ (↑A : Set ℕ))
    (hcΓ : ∀ γ ∈ Γ, c ∉ sentenceJConsts (L' := L) (J := ℕ) γ)
    (hcΔ : ∀ δ ∈ Δ, c ∉ sentenceJConsts (L' := L) (J := ℕ) δ)
    (h : MalitzInsepAt F R A (insert (genEx c φc) Γ) Δ) :
    MalitzInsepAt F R (insert c A) (insert φc Γ) Δ := by
  rintro ⟨σ, huniv, hbf, hbr, hsupp, hΓσ, hΔσ⟩
  have hreal : ∀ (N : Type) [L[[ℕ]].Structure N],
      @Sentenceω.Realize L[[ℕ]] (Theoryω.conjunction Δ hΔc) N _ ↔ Theoryω.Model Δ N :=
    fun N _ => Theoryω.realize_conjunction_iff Δ hΔc N
  refine h ⟨(Theoryω.conjunction Δ hΔc).not, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isUniversal_not _).mpr (isExistential_conjunction Δ hΔc hΔex)
  · intro s hs
    simp only [BoundedFormulaω.baseFunctionsIn, BoundedFormulaω.functionsIn, Set.mem_setOf_eq,
      Set.union_empty] at hs
    exact baseFunctionsIn_conjunction_subset Δ hΔc hΔF hs
  · intro s hs
    simp only [BoundedFormulaω.baseRelationsIn, BoundedFormulaω.relationsIn, Set.mem_setOf_eq,
      Set.union_empty] at hs
    exact baseRelationsIn_conjunction_subset Δ hΔc hΔR hs
  · rw [sentenceJConsts_not]
    exact sentenceJConsts_conjunction_subset Δ hΔc hΔA
  -- `Γ, ∃x φ(x) ⊨ ¬⋀Δ`: a model of both would reinterpret `c` at the witness and realize
  -- `σ(c)` and `¬σ(c)` at once.
  · intro N instN neN hmodel
    show @Sentenceω.Realize L[[ℕ]] (Theoryω.conjunction Δ hΔc).not N instN
    rw [Sentenceω.Realize, BoundedFormulaω.realize_not]
    intro hcon
    have hΔmodel : Theoryω.Model Δ N := (hreal N).mp hcon
    set base := (L.lhomWithConstants ℕ).reduct N with hbase
    set hmap := ambientConstMap (L := L) N with hh
    have bridge : ∀ (ψ : L[[ℕ]].Sentenceω),
        @Sentenceω.Realize L[[ℕ]] ψ N instN
          ↔ @BoundedFormulaω.Realize L[[ℕ]] N (wc base hmap) Empty 0 ψ Empty.elim Fin.elim0 :=
      fun ψ => ambient_realize_iff_wc (S := instN) ψ Empty.elim Fin.elim0
    have hφ : @BoundedFormulaω.Realize L[[ℕ]] N (wc base hmap) Empty 0 (genEx c φc)
        Empty.elim Fin.elim0 := (bridge _).mp (hmodel _ (Set.mem_insert _ _))
    obtain ⟨x, hx⟩ := (realize_genEx base hmap c φc).mp hφ
    have hshift : ∀ (ρ : L[[ℕ]].Sentenceω), c ∉ sentenceJConsts (L' := L) (J := ℕ) ρ →
        @Sentenceω.Realize L[[ℕ]] ρ N instN →
        @BoundedFormulaω.Realize L[[ℕ]] N (wc base (Function.update hmap c x)) Empty 0 ρ
          Empty.elim Fin.elim0 := by
      intro ρ hfresh hρ
      have hg : @BoundedFormulaω.Realize L[[ℕ]] N (wc base hmap) Empty 0 ρ Empty.elim Fin.elim0 :=
        (bridge _).mp hρ
      have hcongr : ∀ k ∈ sentenceJConsts (L' := L) (J := ℕ) ρ,
          hmap k = Function.update hmap c x k := by
        intro k hk
        have hkc : (k : ℕ) ≠ c := fun heq => hfresh (heq ▸ hk)
        exact (Function.update_of_ne (α := ℕ) hkc x hmap).symm
      rwa [BoundedFormulaω.realize_congr_const base ρ hcongr Empty.elim Fin.elim0] at hg
    have hσ : @BoundedFormulaω.Realize L[[ℕ]] N (wc base (Function.update hmap c x)) Empty 0 σ
        Empty.elim Fin.elim0 :=
      @hΓσ N (wc base (Function.update hmap c x)) neN (fun ψ hψ => by
        rcases Set.mem_insert_iff.mp hψ with rfl | hψ
        · exact hx
        · exact hshift ψ (hcΓ ψ hψ) (hmodel _ (Set.mem_insert_of_mem _ hψ)))
    have hnσ : @BoundedFormulaω.Realize L[[ℕ]] N (wc base (Function.update hmap c x)) Empty 0 σ.not
        Empty.elim Fin.elim0 :=
      @hΔσ N (wc base (Function.update hmap c x)) neN
        (fun ψ hψ => hshift ψ (hcΔ ψ hψ) (hΔmodel ψ hψ))
    exact hnσ hσ
  -- `Δ ⊨ ¬¬⋀Δ`
  · intro N instN neN hmodel
    show @Sentenceω.Realize L[[ℕ]] (Theoryω.conjunction Δ hΔc).not.not N instN
    rw [Sentenceω.Realize, BoundedFormulaω.realize_not, BoundedFormulaω.realize_not]
    exact fun hn => hn ((hreal N).mpr hmodel)

end FirstOrder.Language
