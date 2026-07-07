/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.LocalEMTemplateRealization
import InfinitaryLogic.Conditional.MorleyHanfTransfer

/-!
# The Conditional-facing Ω-residual bridge

The one-theorem file connecting the named local-EM seed residual `MorleySeedOmegaExtraction`
(`Methods/LocalEMTemplateRealization.lean`) to the honest Morley–Hanf residual
`MorleySeedTailTemplateRealizable` (`Conditional/MorleyHanfTransfer.lean`):

* `morleySeedTailTemplateRealizable_of_localEMOmega` — `ΓlocalColim`-restricted witness
  homogeneity of the seed extraction implies seed-template realizability, **modulo the bridge's
  extra `[Countable (Σ n, L'.Functions n)]`** (`MorleySeedTailTemplateRealizable` itself assumes
  only countably many relation symbols; removing the extra assumption is the planned
  generated-sublanguage cleanup chunk). Both sides carry the full source facts — `φ` holds in
  `M`, `|M| ≥ ℶ_{ω₁}`, pairwise distinctness — and the realizing model is the
  countable-language EM quotient; the broad `TailTemplateRealizable` over arbitrary sequences is
  false-shaped (see its docstring) and is deliberately NOT the target here.

This file is deliberately isolated, like `LocalEMExtraction.lean`, because it imports
`Conditional/MorleyHanfTransfer.lean`; the template-realization bridge itself
(`LocalEMTemplateRealization.lean`) stays Conditional-free (guarded by
`scripts/check_local_boundary.sh`).

**Audit outcome (end of this file): both seed Ω-residuals are REFUTED.** The height pattern
embeds inside the *true* Morley-seed sentence `badSentence = ∃x, ¬⋀ᵢ Pᵢ(x)`: the successor
family's subformula closure re-imports the divergent conjunction `⋀ᵢ Pᵢ` into `ΓlocalColim`, and
on every subsequence of the height sequence each `Pᵢ` is eventually true while the conjunction
never is — defeating the uniform `iInf`-cutoff. `height_no_seed_omega_homogeneous` (the
diagnostic, for *every* subsequence), `not_morleySeedOmegaHomogeneousExtraction_height`, and
`not_morleySeedOmegaExtraction_height` (the Ω-bundle itself, via `iInf_complete` at the constant
terms) are all axiom-clean. So the honest route to `MorleySeedTailTemplateRealizable` must go
**below** the `OmegaCompleteForColim` bundle: closer to the classical EM/Skolem-hull proof,
using the truth of `φ` in the source model and Skolem closure, rather than demanding arbitrary
`atTop` countable-intersection upgrades from the extracted sequence. The theorems above
(`morleySeedTailTemplateRealizable_of_localEMOmega` etc.) remain true implications, but their
hypotheses are now known to be over-strong; the reshape is the next chunk.
-/

namespace FirstOrder.Language

/-- **The seed Ω-residual discharges the Morley–Hanf residual**: `ΓlocalColim`-restricted
witness homogeneity of the seed extraction (`MorleySeedOmegaExtraction`) implies
`MorleySeedTailTemplateRealizable` — modulo this bridge's extra function-symbol countability.
The size premise supplies `Nonempty M` here (the Skolem stages interpret by Hilbert choice) and
is passed through to the extraction hypothesis, which is free to consume it combinatorially;
the rest is the per-seed acceptance `tailTemplateRealizable_of_localEM`. -/
theorem morleySeedTailTemplateRealizable_of_localEMOmega {L' : Language.{0, 0}}
    [Countable (Σ n, L'.Functions n)] [Countable (Σ l, L'.Relations l)]
    (h : MorleySeedOmegaExtraction L') : MorleySeedTailTemplateRealizable (L' := L') := by
  intro φ M instM a J instJ hSize hφreal hPair hTail
  haveI : Infinite M := by
    rw [Cardinal.infinite_iff]
    exact le_trans (Cardinal.aleph0_le_beth _) hSize
  haveI : Nonempty M := ⟨(Infinite.natEmbedding M) 0⟩
  exact tailTemplateRealizable_of_localEM (morleySeed φ) M a J hTail
    (h φ M a J hSize hφreal hPair hTail)

end FirstOrder.Language

-- lean4:disprove-begin txn=a444a2eb7a18 cycle=1 role=artifact decl=not_morleySeedOmegaExtraction_height
namespace FirstOrder.Language

/-- Realization of a canonical deForm: substituting the `Fin p`-variable terms `gt` for the bound
variables and rebinding realizes as `φ` on the term values. The `J`-free core of
`realize_locDeForm`. -/
theorem realize_canonDeForm {Λ : Language.{0, 0}} {M : Type} [Λ.Structure M] {n p : ℕ}
    (φ : Λ.BoundedFormulaω Empty n) (gt : Fin n → Λ.Term (Fin p)) (xs : Fin p → M) :
    (canonDeForm Λ φ gt).Realize (Empty.elim : Empty → M) xs ↔
      φ.Realize (Empty.elim : Empty → M) (fun i => (gt i).realize xs) := by
  rw [canonDeForm, BoundedFormulaω.realize_relabel_sumInr_zero]
  simp only [Formulaω.Realize, BoundedFormulaω.realize_subst]
  exact realize_openBounds φ _

namespace HeightCex

instance : ∀ n, Countable (Lang.Functions n) := fun _ => inferInstanceAs (Countable Empty)

instance : Countable (Σ n, Lang.Functions n) := inferInstance

/-- The bad seed sentence `∃x, ¬⋀ᵢ Pᵢ(x)` — **true** in the height model, yet hiding the
divergent countable conjunction as a subformula. -/
def badSentence : Lang.Sentenceω := conj.not.ex

/-- `badSentence` holds in the height model: every element has finite height. -/
theorem realize_badSentence : Sentenceω.Realize badSentence Carrier := by
  show BoundedFormulaω.Realize (conj.not.ex) (Empty.elim : Empty → Carrier) Fin.elim0
  rw [BoundedFormulaω.realize_ex]
  exact ⟨a 0, by rw [BoundedFormulaω.realize_not]; exact not_realize_conj _ _⟩

/-- `disEqFormula` holds on every strictly monotone tuple of `a` (the sequence is injective). -/
theorem realize_disEq_of_strictMono {u : Fin 2 → ℕ} (hu : StrictMono u) :
    (disEqFormula : Lang.BoundedFormulaω Empty 2).Realize (Empty.elim : Empty → Carrier)
      (a ∘ u) := by
  simp only [disEqFormula, BoundedFormulaω.realize_not, BoundedFormulaω.realize_equal,
    Term.realize_var]
  intro heq
  have h01 : u 0 ≠ u 1 := ne_of_lt (hu (show (0 : Fin 2) < 1 by decide))
  exact h01 (emb.injective heq)

/-- `a` is tail-indiscernible on the Morley seed of `badSentence`: the sentence member is
tuple-independent (arity `0`), and the disequality member is constantly true on strictly
monotone tuples. -/
theorem tail_indisc_morleySeed :
    IsLomega1omegaIndiscernibleOnTail (L := Lang) a (Set.range (morleySeed badSentence)) := by
  rintro n φ ⟨k, hk⟩
  match k, hk with
  | 0, hk =>
    cases hk
    exact ⟨0, fun u v _ _ _ _ => by
      rw [show (a ∘ u : Fin 0 → Carrier) = a ∘ v from funext fun j => j.elim0]⟩
  | 1, hk =>
    cases hk
    exact ⟨0, fun u v hu hv _ _ =>
      iff_of_true (realize_disEq_of_strictMono hu) (realize_disEq_of_strictMono hv)⟩
  | k + 2, hk =>
    cases hk
    exact ⟨0, fun u v _ _ _ _ => by
      rw [show (a ∘ u : Fin 0 → Carrier) = a ∘ v from funext fun j => j.elim0]⟩

/-- The seed stage of the bad sentence. -/
abbrev badStage : LocalStage := LocalStage.ofSeq Lang (morleySeed badSentence)

/-- The countable conjunction reaches the successor family: it is an iterated subformula of the
lifted `badSentence = ((⋀ᵢPᵢ).not.not.all).not`. -/
theorem conj_mem_Γlocal_one :
    (⟨1, conj.mapLanguage (LlocalHom badStage 0)⟩ :
      Σ n, (Llocal badStage 1).BoundedFormulaω Empty n) ∈ Γlocal badStage 1 := by
  have h0 : (⟨0, badSentence⟩ : Σ n, Lang.BoundedFormulaω Empty n) ∈ Γlocal badStage 0 :=
    ⟨0, rfl⟩
  have h1 := liftGamma_mem_Γlocal_succ badStage h0
  have h2 : (⟨0, ((conj.mapLanguage (LlocalHom badStage 0)).not.not).all⟩ :
      Σ n, (Llocal badStage 1).BoundedFormulaω Empty n) ∈ Γlocal badStage 1 :=
    bfSubformulas_subset_Γlocal_succ badStage h1 (Set.mem_insert _ _)
  have h3 : (⟨1, (conj.mapLanguage (LlocalHom badStage 0)).not.not⟩ :
      Σ n, (Llocal badStage 1).BoundedFormulaω Empty n) ∈ Γlocal badStage 1 :=
    bfSubformulas_subset_Γlocal_succ badStage h2 rfl
  have h4 : (⟨1, (conj.mapLanguage (LlocalHom badStage 0)).not⟩ :
      Σ n, (Llocal badStage 1).BoundedFormulaω Empty n) ∈ Γlocal badStage 1 :=
    bfSubformulas_subset_Γlocal_succ badStage h3 (Set.mem_insert _ _)
  exact bfSubformulas_subset_Γlocal_succ badStage h4 (Set.mem_insert _ _)

/-- The countable conjunction's colimit image — in the disjunction/conjunction shape the
Ω-clauses quantify over — lies in the colimit family. -/
theorem conj_mem_ΓlocalColim :
    (⟨1, BoundedFormulaω.iInf (fun i => (P i).mapLanguage (LlocalInclusion badStage 0))⟩ :
      Σ n, (localColim badStage).BoundedFormulaω Empty n) ∈ ΓlocalColim badStage := by
  have h : (⟨1, (conj.mapLanguage (LlocalHom badStage 0)).mapLanguage
        (LlocalInclusion badStage 1)⟩ :
      Σ n, (localColim badStage).BoundedFormulaω Empty n) ∈ ΓlocalColim badStage :=
    toLocalColimFormula_mem_ΓlocalColim badStage conj_mem_Γlocal_one
  rwa [mapLanguage_LlocalInclusion_lift badStage] at h

/-- The de-substituted component computation: the canonical deForm of `Pᵢ`'s colimit image, along
the identity tuple, holds on the consecutive `(a ∘ g)`-tuple at depth `d` iff `i ≤ g d`. -/
theorem canonDeForm_P_iff (g : ℕ ↪o ℕ) (i d : ℕ) :
    letI : (localColim badStage).Structure Carrier := localColimStructure badStage
    ((canonDeForm (localColim badStage) ((P i).mapLanguage (LlocalInclusion badStage 0))
        (fun _ : Fin 1 => Term.var (0 : Fin 1))).Realize (Empty.elim : Empty → Carrier)
      (fun k : Fin 1 => (a ∘ ⇑g) (d + (k : ℕ))) ↔ i ≤ g d) := by
  letI : (localColim badStage).Structure Carrier := localColimStructure badStage
  have hxs : (P i).Realize (Empty.elim : Empty → Carrier) (fun _ : Fin 1 => emb (g d))
      ↔ i ≤ g d := by
    rw [realize_P]
    show i ≤ hgt (emb (g d)) ↔ i ≤ g d
    rw [hgt_emb]
  exact (realize_canonDeForm _ _ _).trans
    ((realize_map_LlocalInclusion badStage 0 (P i) (Empty.elim : Empty → Carrier) _).trans hxs)

/-- **The sharper diagnostic**: NO subsequence of the height sequence is source-side
Ω-homogeneous for the bad-sentence seed stage — the uniform `iInf`-cutoff fails at the hidden
conjunction: each `Pᵢ(a (g d))` is eventually true, but at every depth `d` the component
`i = g d + 1` fails. -/
theorem height_no_seed_omega_homogeneous (g : ℕ ↪o ℕ) :
    letI : (localColim badStage).Structure Carrier := localColimStructure badStage
    ¬ LocalEMOmegaHomogeneous badStage (a ∘ ⇑g) := by
  letI : (localColim badStage).Structure Carrier := localColimStructure badStage
  intro hhom
  have hcut := hhom.iInf_homogeneous
    (fun i => (P i).mapLanguage (LlocalInclusion badStage 0)) conj_mem_ΓlocalColim
    (fun _ : Fin 1 => Term.var (0 : Fin 1))
    (fun i => Filter.eventually_atTop.mpr
      ⟨i, fun d hd => (canonDeForm_P_iff g i d).mpr (le_trans hd g.strictMono.le_apply)⟩)
  rw [Filter.eventually_atTop] at hcut
  obtain ⟨d₀, hd₀⟩ := hcut
  have h := (canonDeForm_P_iff g (g d₀ + 1) d₀).mp (hd₀ d₀ (le_refl d₀) (g d₀ + 1))
  omega

end HeightCex

/-- **The seed homogeneity residual is refutable**: `MorleySeedOmegaHomogeneousExtraction` fails
at the height language — the bad seed sentence `∃x, ¬⋀ᵢ Pᵢ(x)` is *true* in the height model
(so all source facts hold), yet the hidden conjunction defeats the uniform `iInf`-cutoff on
every subsequence. The seed restriction does not save the source-side Ω-homogeneity shape. -/
theorem not_morleySeedOmegaHomogeneousExtraction_height :
    ¬ MorleySeedOmegaHomogeneousExtraction HeightCex.Lang := by
  intro h
  obtain ⟨g, _hind, hhom⟩ := h HeightCex.badSentence HeightCex.Carrier HeightCex.a
    (ge_of_eq HeightCex.mk_Carrier) HeightCex.realize_badSentence
    (fun i j hij hEq => hij (HeightCex.emb.injective hEq)) HeightCex.tail_indisc_morleySeed
  exact HeightCex.height_no_seed_omega_homogeneous g hhom

/-- **The seed Ω-bundle residual is refutable too**: `MorleySeedOmegaExtraction` fails at the
height language — for *any* extracted context with `ctx.a = a ∘ g`, the support-covered
`iInf_complete` clause at the hidden conjunction (over the constant terms `c₀`, support `{0}`)
demands exactly the failing uniform cutoff. So the reshape must go below the
`OmegaCompleteForColim` bundle itself, not merely below source-side homogeneity. -/
theorem not_morleySeedOmegaExtraction_height :
    ¬ MorleySeedOmegaExtraction HeightCex.Lang := by
  intro h
  obtain ⟨g, ctx, hctxa, _hctxΓ, hc⟩ := h HeightCex.badSentence HeightCex.Carrier HeightCex.a ℕ
    (ge_of_eq HeightCex.mk_Carrier) HeightCex.realize_badSentence
    (fun i j hij hEq => hij (HeightCex.emb.injective hEq)) HeightCex.tail_indisc_morleySeed
  letI : (localColim HeightCex.badStage).Structure HeightCex.Carrier :=
    localColimStructure HeightCex.badStage
  set ts : Fin 1 → (localColim HeightCex.badStage)[[ℕ]].Term Empty :=
    fun _ => Term.func
      (Sum.inr (0 : ℕ) : (localColim HeightCex.badStage)[[ℕ]].Functions 0) Fin.elim0 with hts
  have hcov : ∀ i, locJSupport (localColim HeightCex.badStage) ℕ (ts i) ⊆ ({0} : Finset ℕ) := by
    intro i
    show locJSupport (localColim HeightCex.badStage) ℕ
      (Term.func (Sum.inr (0 : ℕ) : (localColim HeightCex.badStage)[[ℕ]].Functions 0)
        Fin.elim0) ⊆ ({0} : Finset ℕ)
    rw [locJSupport_constTerm]
  have hkey : ∀ (i d : ℕ),
      (((HeightCex.P i).mapLanguage (LlocalInclusion HeightCex.badStage 0)).Realize
          (Empty.elim : Empty → HeightCex.Carrier)
          (fun j => locDeepInterp (localColim HeightCex.badStage) ℕ ctx.a d ({0} : Finset ℕ)
            (ts j)) ↔ i ≤ g d) := by
    intro i d
    have hxs : (HeightCex.P i).Realize (Empty.elim : Empty → HeightCex.Carrier)
        (fun _ : Fin 1 => ctx.a (d + deepRank ℕ ({0} : Finset ℕ) 0)) ↔ i ≤ g d := by
      rw [HeightCex.realize_P, hctxa]
      show i ≤ HeightCex.hgt (HeightCex.emb (g d)) ↔ i ≤ g d
      rw [HeightCex.hgt_emb]
    exact (realize_map_LlocalInclusion HeightCex.badStage 0 (HeightCex.P i)
      (Empty.elim : Empty → HeightCex.Carrier) _).trans hxs
  have hED : ∀ i : ℕ, LocalEMContext.eventualDeepTruth (Λ := localColim HeightCex.badStage)
      (J := ℕ) ctx ((HeightCex.P i).mapLanguage (LlocalInclusion HeightCex.badStage 0)) ts
      ({0} : Finset ℕ) := by
    intro i
    rw [LocalEMContext.eventualDeepTruth, Filter.eventually_atTop]
    exact ⟨i, fun d hd => (hkey i d).mpr (le_trans hd g.strictMono.le_apply)⟩
  have hcontra := hc.iInf_complete
    (fun i => (HeightCex.P i).mapLanguage (LlocalInclusion HeightCex.badStage 0))
    HeightCex.conj_mem_ΓlocalColim ts ({0} : Finset ℕ) hcov hED
  rw [LocalEMContext.eventualDeepTruth, Filter.eventually_atTop] at hcontra
  obtain ⟨d₀, hd₀⟩ := hcontra
  have hall := hd₀ d₀ (le_refl d₀)
  rw [BoundedFormulaω.realize_iInf] at hall
  have := (hkey (g d₀ + 1) d₀).mp (hall (g d₀ + 1))
  omega

end FirstOrder.Language
-- lean4:disprove-end txn=a444a2eb7a18
