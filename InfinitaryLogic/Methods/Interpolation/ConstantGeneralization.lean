/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.Interpolation.ConstantElimination
import InfinitaryLogic.Lomega1omega.QuantifierClass
import InfinitaryLogic.Lomega1omega.Theory

/-!
# Constant generalization: the `∀`-twin of `genEx`, and countable-conjunction bounds

Neutral companion to `ConstantElimination.lean`.  Where `genEx j ρ` existentially generalizes the
constant `c_j` out of a sentence, `genAll j ρ` generalizes it **universally**, with the matching
realization lemma, occurrence calculus, and the two entailment-acceptance sequents:

* `entails_genAll_of_entails` (side 1): `Γ ⊨ σ(c) ⟹ Γ ⊨ ∀x σ(x)`, `c` fresh for `Γ`.  Unlike
  `genEx`'s side-1 sequent this genuinely **needs** freshness — `∀`-introduction is not weakening;
* `entails_not_genAll_of_entails_not` (side 2): `Δ, δ(c) ⊨ ¬σ(c) ⟹ Δ, ∃x δ(x) ⊨ ¬∀x σ(x)`,
  `c` fresh for `Δ`.

`genAll` is **class-preserving** for the quantifier hierarchy of `Lomega1omega/QuantifierClass.lean`
(`isUniversal_genAll`), because `all` is admissible at the universal sign and neither constant
abstraction nor `relabel` moves the class; `genEx`, dually, is never universal
(`not_isUniversal_genEx`).  That pair of facts is what makes an asymmetric separator class possible
at all, so both live here rather than inside any one consumer.

The second half collects the class and occurrence bounds for `Theoryω.conjunction`, the
countable conjunction of a theory: existentiality and the three symbol/support bounds descend from
the members.

Nothing here is specific to Malitz interpolation (issue #15) or to end extensions (issue #16); both
consume it.
-/

namespace FirstOrder.Language

open FirstOrder Structure BoundedFormulaω

variable {L : Language.{0, 0}} {M : Type}
variable {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}

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

/-! ## Bounds for the countable conjunction of a theory -/

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

end FirstOrder.Language
