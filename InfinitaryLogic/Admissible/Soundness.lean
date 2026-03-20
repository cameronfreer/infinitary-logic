/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.ProofSystem
import InfinitaryLogic.ModelExistence.SatisfiableConsistencyProperty

/-!
# Soundness of the Proof System

This file proves soundness of the proof system for admissible fragments: derivable
sentences are true in all models equipped with a naming function.

## Main Results

- `Derivable.sound`: If `Derivable A T φ`, then `φ` is true in any model of `T`
  with a naming function.
- `AConsistent.of_has_model`: A theory with a model (equipped with a naming function)
  is consistent.

## Design Notes

The naming function is needed because the omega-rule (`all_intro`) derives `∀x.φ(x)`
from derivations of `φ(t)` for all closed terms `t`. Soundness requires that every
element of the model is named by some closed term.

The `all_intro`/`all_elim` cases require a compatibility lemma between `openBounds`,
`subst`, and `Realize`, which involves subtle interactions between bound and free
variable representations. These cases use `realize_openBounds` (the semantic roundtrip
for `openBounds`) together with `realize_subst` and `Fin.snoc_elim0_eq`.
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure BoundedFormulaω

/-- **Soundness**: If `φ` is derivable from `T` in fragment `A`, then `φ` is true
in any model of `T` equipped with a naming function. -/
theorem Derivable.sound {A : AdmissibleFragment L}
    {T : Set L.Sentenceω} {φ : L.Sentenceω}
    (hd : Derivable A T φ)
    {M : Type w} [L.Structure M]
    (hNF : NamingFunction L M)
    (hM : Theoryω.Model T M) :
    Sentenceω.Realize φ M := by
  -- Induction on the derivation. Since T and φ are indices, hM gets generalized.
  induction hd with
  | assumption h _ => exact hM _ h
  | weaken hsub _ ih => exact ih (Theoryω.Model.mono hsub hM)
  | falsum_elim _ _ ih => exact absurd (ih hM) id
  | imp_intro _ _ ih =>
    show Sentenceω.Realize (BoundedFormulaω.imp _ _) M
    simp only [Sentenceω.Realize, realize_imp]
    intro hφ
    apply ih
    intro ψ hψ
    rcases hψ with hψ_T | hψ_eq
    · exact hM ψ hψ_T
    · rw [Set.mem_singleton_iff.mp hψ_eq]; exact hφ
  | imp_elim _ _ ih₁ ih₂ =>
    have h₁ := ih₁ hM
    simp only [Sentenceω.Realize, realize_imp] at h₁
    exact h₁ (ih₂ hM)
  | not_not_elim _ ih =>
    have h := ih hM
    simp only [Sentenceω.Realize, realize_not] at h
    by_contra hc
    exact h hc
  | iInf_intro _ _ ih =>
    show Sentenceω.Realize (.iInf _) M
    simp only [Sentenceω.Realize, realize_iInf]
    intro k; exact ih k hM
  | iInf_elim k _ ih =>
    have h := ih hM
    simp only [Sentenceω.Realize, realize_iInf] at h
    exact h k
  | iSup_intro k _ _ ih =>
    show Sentenceω.Realize (.iSup _) M
    simp only [Sentenceω.Realize, realize_iSup]
    exact ⟨k, ih hM⟩
  | iSup_elim _ _ ih₁ ih₂ =>
    have h₁ := ih₁ hM
    simp only [Sentenceω.Realize, realize_iSup] at h₁
    obtain ⟨k, hk⟩ := h₁
    apply ih₂ k
    intro ψ hψ
    rcases hψ with hψ_T | hψ_eq
    · exact hM ψ hψ_T
    · rw [Set.mem_singleton_iff.mp hψ_eq]; exact hk
  | all_intro φ _ _ ih =>
    -- Need: ∀ m : M, φ.Realize Empty.elim (Fin.snoc Fin.elim0 m)
    -- IH: for all t, T ⊨ (φ.openBounds.subst t)
    show Sentenceω.Realize φ.all M
    simp only [Sentenceω.Realize, realize_all]
    intro m
    have h := ih (hNF.name m) hM
    simp only [Sentenceω.Realize, realize_subst] at h
    -- h : (φ.openBounds).Realize (fun _ => (hNF.name m).realize Empty.elim) Fin.elim0
    -- which is Formulaω.Realize (φ.openBounds) (fun _ => (hNF.name m).realize Empty.elim)
    have h' := (realize_openBounds φ (fun _ => (hNF.name m).realize (Empty.elim : Empty → M))).mp h
    rw [hNF.sound m] at h'
    rwa [Fin.snoc_elim0_eq]
  | all_elim φ t _ ih =>
    -- Need: (φ.openBounds.subst (fun _ => t)).Realize Empty.elim Fin.elim0
    -- IH: T ⊨ φ.all
    have h := ih hM
    simp only [Sentenceω.Realize, realize_all] at h
    specialize h (t.realize (Empty.elim : Empty → M))
    rw [Fin.snoc_elim0_eq] at h
    simp only [Sentenceω.Realize, realize_subst]
    exact (realize_openBounds φ (fun _ => t.realize (Empty.elim : Empty → M))).mpr h
  | eq_refl t _ =>
    simp only [Sentenceω.Realize, realize_equal]
  | eq_subst t₁ t₂ ψ _ _ _ ih₁ ih₂ =>
    -- Equality substitution: t₁ = t₂ and ψ(t₁) imply ψ(t₂)
    have heq := ih₁ hM
    have hψ := ih₂ hM
    simp only [Sentenceω.Realize, realize_equal, Term.realize_relabel,
      Sum.elim_comp_inl, realize_subst] at heq hψ ⊢
    -- heq : t₁.realize Empty.elim = t₂.realize Empty.elim
    -- hψ : ψ.Realize (fun _ => t₁.realize Empty.elim) Fin.elim0
    -- Goal: ψ.Realize (fun _ => t₂.realize Empty.elim) Fin.elim0
    have key : (fun (_ : Fin 1) => t₁.realize (Empty.elim : Empty → M)) =
               (fun (_ : Fin 1) => t₂.realize (Empty.elim : Empty → M)) := by
      funext; exact heq
    rw [key] at hψ
    exact hψ
  | em φ _ =>
    show Sentenceω.Realize (φ.or φ.not) M
    simp only [Sentenceω.Realize, realize_or, realize_not]
    exact Classical.em _

/-- A theory with a model (equipped with a naming function) is consistent. -/
theorem AConsistent.of_has_model {A : AdmissibleFragment L}
    {T : Set L.Sentenceω}
    {M : Type w} [L.Structure M]
    (hNF : NamingFunction L M)
    (hM : Theoryω.Model T M)
    (_hT : T ⊆ A.formulas) :
    AConsistent A T := by
  intro hd
  exact hd.sound hNF hM

end Language

end FirstOrder
