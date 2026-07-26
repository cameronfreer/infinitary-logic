/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.Interpolation.Inseparability
import InfinitaryLogic.Methods.Interpolation.ConstantGeneralization

/-!
# The two-sided C7 spike for a universal separator class (issue #15, Unit 2)

The stop/go gate of `docs/malitz-audit.md` §D4.  `MalitzInsepAt` is `InsepAt` with the separator
additionally required to be **universal**; the question is whether the two fresh-witness (C7)
closure steps survive that restriction under candidate 1 —

> `Γ` unrestricted, `Δ` existential, separator universal.

The generic constant-generalization machinery this needs (`genAll`, its realization and occurrence
calculus, the quantifier class of constant abstraction, and the countable-conjunction bounds) is
neutral and lives in `ConstantGeneralization.lean`.  Only the Malitz-specific predicate and the two
gates are here.

**Right trigger (witness added on the `Δ` side) — clean.**  `genAll` is class-preserving, so
`malitzInsepAt_witness_of_genAll` holds with **no side conditions beyond freshness** — exactly the
shape of the existing Craig/Lyndon gates.

**Left trigger (witness added on the `Γ` side) — closes, but not inside the shared vocabulary.**
`genEx` is not class-preserving (`not_isUniversal_genEx`: `∃x σ(x)` is `Σ2` for universal `σ`) — a
fact about the *construction*, not by itself a failure of the closure.  The replacement is the
audit's finite-existential-side conjunction: with `Δ` existential, `δΔ := ⋀ Δ` is existential, so
`¬δΔ` is universal, `Δ ⊨ ¬¬δΔ` is trivial, and `Γ, ∃x φ(x) ⊨ ¬δΔ` because a model of both would
reinterpret the fresh `c` at the existential witness, keeping `Γ` and `Δ` standing and producing
`σ(c)` and `¬σ(c)` at once.

`malitzInsepAt_witness_of_existentialDelta` formalizes that, at the price of three hypotheses on
`Δ`:

```
hΔA : ∀ δ ∈ Δ, sentenceJConsts δ ⊆ ↑A       -- free: PairedInsepFamilyMem already carries it
hΔF : ∀ δ ∈ Δ, δ.baseFunctionsIn ⊆ F        -- NOT free
hΔR : ∀ δ ∈ Δ, δ.baseRelationsIn ⊆ R        -- NOT free
```

In the interpolation family the separator budget is the *shared* vocabulary `(F₁ ∩ F₂, R₁ ∩ R₂)`
while `Δ ⊆ SentBnd F₂ R₂`, so `¬δΔ` is legal only when `F₂ ⊆ F₁` and `R₂ ⊆ R₁`.  That is not a
formalization artifact: a separator built out of `Δ` is exactly what the shared-vocabulary condition
forbids.

**Scope of the verdict** (audit §D4/§D4.5).  This resolves D4 for the *existing* C7 strategies only:
candidate 2 is ruled out for **this paired-family closure argument**, not refuted for every possible
architecture, and candidate 3 remains open.  In particular the two hypotheses are not dischargeable
by widening the budget: the settings that supply the vocabulary hypothesis (a relativized
preservation encoding, where the right coordinate's language is contained in the left's) are exactly
the settings whose right root is an arbitrary `σ ∧ ¬φ` and so **fails** `hΔex`, while the setting
that supplies `hΔex` — Theorem 4.5, whose right root `ψ.not` is existential precisely because `ψ` is
universal — is the one with a genuinely shared vocabulary.
-/

namespace FirstOrder.Language

open FirstOrder Structure BoundedFormulaω

variable {L : Language.{0, 0}} {M : Type} {Γ Δ : Set L[[ℕ]].Sentenceω}

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
