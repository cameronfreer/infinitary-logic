/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.LocalEMTemplateRealization
import InfinitaryLogic.Methods.GeneratedSublanguage
import InfinitaryLogic.Conditional.MorleyHanfTransfer

/-!
# The Conditional-facing Ω-residual bridge

The one-theorem file connecting the named local-EM seed residual `MorleySeedOmegaExtraction`
(`Methods/LocalEMTemplateRealization.lean`) to the honest Morley–Hanf residual
`MorleySeedTailTemplateRealizable` (`Conditional/MorleyHanfTransfer.lean`):

* `morleySeedTailTemplateRealizable_of_localEMOmega` — `ΓlocalColim`-restricted witness
  homogeneity of the seed extraction implies seed-template realizability (kept as a diagnostic
  artifact; it still carries the extra `[Countable (Σ n, L'.Functions n)]`). Both sides carry
  the full source facts — `φ` holds in `M`, `|M| ≥ ℶ_{ω₁}`, pairwise distinctness — and the
  realizing model is the countable-language EM quotient; the broad `TailTemplateRealizable`
  over arbitrary sequences is false-shaped (see its docstring) and is deliberately NOT the
  target here.

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
**below** the `OmegaCompleteForColim` bundle. The theorems above
(`morleySeedTailTemplateRealizable_of_localEMOmega` etc.) remain true implications, but their
hypotheses are known to be over-strong — they are kept as refutation/diagnostic artifacts only.

**The reshape (end of this file): the full-indiscernibility route.**
`morleySeedTailTemplateRealizable_of_morleyHanfExtraction` wires the classical extraction
residual `MorleyHanfExtraction` — a **fresh, fully indiscernible** sequence from `M`, where the
`ℶ_{ω₁}` premise does real combinatorial work — through
`omegaCompleteForColim_of_indiscernibleOn` (full indiscernibility kills the witness drift) and
the absolute Morley-seed template agreement, into the existing truth-lemma pipeline; the
endpoint `morley_hanf_of_morleyHanfExtraction` derives the Hanf bound from the extraction alone.

**Second audit outcome (statement audit 2026-07-07): `MorleyHanfExtraction` is itself
FALSE-SHAPED** — full in-`M` indiscernibility of an `ω`-sequence on an arbitrary countable
family implies the ZFC-refutable partition relation `ℶ_ω₁ → (ω)^{<ω}_2` (Erdős-cardinal
argument; see the `PureColoringHypothesis` docstring in `Conditional/MorleyHanfTransfer.lean`).
The wiring above remains a true implication and the truth-lemma pipeline it exercises is fully
proved, but the extraction hypothesis cannot be discharged: the classical route (Marker §5.2)
never extracts indiscernibles inside `M` — it certifies an EM template through a consistency
property using per-arity **bounded** Erdős–Rado approximations (now proved:
`finiteArityErdosRadoBounded`, `Combinatorics/FiniteArityErdosRadoInduction.lean`) and
materializes the sequence only in the model built by Model Existence. Reshaping the residual
into that template/consistency-property form is the next design chunk.

**Countability cleanup (also this file):** the endpoints assume only
`[Countable (Σ l, L'.Relations l)]` — the tower's function-symbol countability is discharged by
running the construction in the **generated sublanguage** of `φ`
(`Methods/GeneratedSublanguage.lean`) and expanding the resulting EM quotient back to `L'[[J]]`
(`expandFunStructure` + `realize_templateSentence_expand`; missing symbols act arbitrarily on
the nonempty carrier, and the degenerate `IsEmpty J` case is served by `M` itself,
`morleySeed_theory_model_of_isEmptyJ`). So the proved implication surface is exactly
`MorleyHanfExtraction → Morley–Hanf`, with no local-EM caveats — with the hypothesis itself
false-shaped per the second audit outcome above.
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

/-! ## The full-indiscernibility route (the honest one)

The refuted residuals above all extracted a subsequence of the *given* sequence; the honest route
extracts a **fresh, fully indiscernible** sequence from `M` — the classical Erdős–Rado shape
`MorleyHanfExtraction`, where the `ℶ_{ω₁}` premise does real combinatorial work (e.g. in the
height model the extraction must leave the growing diagonal for a single large height fiber).
Full indiscernibility kills the witness drift (`omegaCompleteForColim_of_indiscernibleOn`), the
Morley seed's template values are absolute (`morleySeed_template_agreement` — no subsequence
relation to the input is needed), and the whole existing truth-lemma pipeline goes through. -/

open Classical in
/-- **Expansion of a sublanguage `[[J]]`-structure to the full language**: function symbols of
the generating set act as before (via the subtype), missing function symbols act arbitrarily
(hence `[Nonempty N]`), constants and all relations pass through (the generated sublanguage
keeps every relation). -/
@[reducible] noncomputable def expandFunStructure {L : Language.{0, 0}} (F : Set (Σ n, L.Functions n))
    (J : Type) {N : Type} [Nonempty N] [instN : (funSublang (L := L) F)[[J]].Structure N] :
    L[[J]].Structure N where
  funMap := fun {m} f xs =>
    match f with
    | Sum.inl f' =>
      if h : (⟨m, f'⟩ : Σ n, L.Functions n) ∈ F then
        Structure.funMap (L := (funSublang (L := L) F)[[J]])
          (Sum.inl (⟨f', h⟩ : (funSublang (L := L) F).Functions m)) xs
      else Classical.arbitrary N
    | Sum.inr c => Structure.funMap (L := (funSublang (L := L) F)[[J]]) (Sum.inr c) xs
  RelMap := fun {_} r xs =>
    match r with
    | Sum.inl r' => Structure.RelMap (L := (funSublang (L := L) F)[[J]]) (Sum.inl r') xs
    | Sum.inr c => Structure.RelMap (L := (funSublang (L := L) F)[[J]]) (Sum.inr c) xs

/-- **Template sentences transfer along the expansion**: the full-language template sentence of
a restricted formula's image holds in the expanded structure iff the sublanguage template
sentence holds in the original — the skeleton constants agree definitionally, and the language
maps peel off through the expansion property (`dif_pos` on the generating set). -/
theorem realize_templateSentence_expand {L : Language.{0, 0}} {F : Set (Σ n, L.Functions n)}
    (J : Type) [LinearOrder J] {N : Type} [Nonempty N]
    [instN : (funSublang (L := L) F)[[J]].Structure N]
    {n : ℕ} (ψ₀ : (funSublang (L := L) F).BoundedFormulaω Empty n) (t : Fin n ↪o J) :
    letI : L[[J]].Structure N := expandFunStructure F J
    (Sentenceω.Realize
        (Lomega1omegaTemplate.templateSentence (ψ₀.mapLanguage (funSublangIncl F)) t) N ↔
      Sentenceω.Realize (Lomega1omegaTemplate.templateSentence ψ₀ t) N) := by
  classical
  letI instE : L[[J]].Structure N := expandFunStructure F J
  refine (realize_templateSentence_of_structure (L := L) (J := J) (N := N)
    (ψ₀.mapLanguage (funSublangIncl F)) t).trans
    (Iff.trans ?_ (realize_templateSentence_of_structure (L := funSublang (L := L) F)
      (J := J) (N := N) ψ₀ t).symm)
  letI : L.Structure N := (L.lhomWithConstants J).reduct N
  letI : (funSublang (L := L) F).Structure N :=
    ((funSublang (L := L) F).lhomWithConstants J).reduct N
  haveI : (funSublangIncl F).IsExpansionOn N := by
    constructor
    · intro m f xs
      show (if h : (⟨m, f.1⟩ : Σ n, L.Functions n) ∈ F then
          Structure.funMap (L := (funSublang (L := L) F)[[J]])
            (Sum.inl (⟨f.1, h⟩ : (funSublang (L := L) F).Functions m)) xs
        else Classical.arbitrary N) = _
      rw [dif_pos f.2]
      rfl
    · intro m r xs
      rfl
  have htup : (fun i => (Term.func (Sum.inr (t i) : L[[J]].Functions 0)
        Fin.elim0 : L[[J]].Term Empty).realize (Empty.elim : Empty → N))
      = (fun i => (Term.func (Sum.inr (t i) : (funSublang (L := L) F)[[J]].Functions 0)
          Fin.elim0 : (funSublang (L := L) F)[[J]].Term Empty).realize
          (Empty.elim : Empty → N)) := by
    funext i
    show Structure.funMap (L := L[[J]]) (Sum.inr (t i) : L[[J]].Functions 0)
        (fun j => ((Fin.elim0 : Fin 0 → L[[J]].Term Empty) j).realize
          (Empty.elim : Empty → N))
      = Structure.funMap (L := (funSublang (L := L) F)[[J]])
        (Sum.inr (t i) : (funSublang (L := L) F)[[J]].Functions 0)
        (fun j => ((Fin.elim0 : Fin 0 → (funSublang (L := L) F)[[J]].Term Empty) j).realize
          (Empty.elim : Empty → N))
    rw [show (fun j => ((Fin.elim0 : Fin 0 → L[[J]].Term Empty) j).realize
        (Empty.elim : Empty → N)) = (Fin.elim0 : Fin 0 → N) from funext fun j => j.elim0,
      show (fun j => ((Fin.elim0 : Fin 0 → (funSublang (L := L) F)[[J]].Term Empty) j).realize
        (Empty.elim : Empty → N)) = (Fin.elim0 : Fin 0 → N) from funext fun j => j.elim0]
    rfl
  rw [htup]
  exact BoundedFormulaω.realize_mapLanguage (funSublangIncl F) ψ₀ (Empty.elim : Empty → N) _

/-- **Morley-seed tail-template realizability from the classical extraction** — with NO
function-symbol countability assumption on `L'` (only the ambient countable relations, matching
`MorleySeedTailTemplateRealizable` itself): the construction runs in the **generated
sublanguage** of `φ` (`funSublang φ.functionsIn`, whose function-symbol countability is proved,
not assumed), and the resulting EM quotient is expanded back to `L'[[J]]` — missing symbols act
arbitrarily on the (nonempty, via the skeleton class of any `j : J`) carrier; the degenerate
`IsEmpty J` case is served by `M` itself. The realizing model is the EM quotient of a **fresh**
fully indiscernible extraction from `M` (`MorleyHanfExtraction`, where the `ℶ_{ω₁}` premise does
real Erdős–Rado work) — not a subsequence of the input `a`; the input's template is matched on
the seed by the absolute-value agreement. HISTORICAL: the extraction residual it consumes was
later shown false in ZFC, and the Morley–Hanf chain is now fully proved by the schema route
(`morleySeedTailTemplateRealizable_holds`); this bridge remains a valid implication and the
record of the pre-schema architecture. -/
theorem morleySeedTailTemplateRealizable_of_morleyHanfExtraction {L' : Language.{0, 0}}
    [Countable (Σ l, L'.Relations l)]
    (hExtract : ∀ (L'' : Language.{0, 0}) [Countable (Σ l, L''.Relations l)],
      MorleyHanfExtraction (L' := L'')) :
    MorleySeedTailTemplateRealizable (L' := L') := by
  intro φ M instM a J instJ hSize hφreal hPair _hTail
  haveI : Infinite M := by
    rw [Cardinal.infinite_iff]
    exact le_trans (Cardinal.aleph0_le_beth _) hSize
  haveI : Nonempty M := ⟨(Infinite.natEmbedding M) 0⟩
  rcases isEmpty_or_nonempty J with hJe | hJne
  · exact morleySeed_theory_model_of_isEmptyJ φ a J hφreal
  -- the generated sublanguage of φ and the restricted seed sentence
  haveI : Countable (Σ n, (funSublang (L := L') φ.functionsIn).Functions n) :=
    funSublang_fun_countable φ.functionsIn_countable
  haveI : Countable (Σ l, (funSublang (L := L') φ.functionsIn).Relations l) :=
    funSublang_rel_countable _
  letI : (funSublang (L := L') φ.functionsIn).Structure M :=
    (funSublangIncl φ.functionsIn).reduct M
  haveI : (funSublangIncl (L := L') φ.functionsIn).IsExpansionOn M :=
    LHom.isExpansionOn_reduct _ _
  have hφ₀map : (φ.restrictFuns (subset_refl _)).mapLanguage (funSublangIncl φ.functionsIn)
      = φ := BoundedFormulaω.mapLanguage_restrictFuns φ (subset_refl _)
  have hφ₀real : Sentenceω.Realize (φ.restrictFuns (subset_refl _) :
      (funSublang (L := L') φ.functionsIn).Sentenceω) M := by
    have h := BoundedFormulaω.realize_mapLanguage (funSublangIncl φ.functionsIn)
      (φ.restrictFuns (subset_refl _)) (Empty.elim : Empty → M) Fin.elim0
    rw [hφ₀map] at h
    exact h.mp hφreal
  -- the local EM construction over the sublanguage seed
  set s₀' := LocalStage.ofSeq (funSublang (L := L') φ.functionsIn)
    (morleySeed (φ.restrictFuns (subset_refl _))) with hs₀'
  letI : (localColim s₀').Structure M := localColimStructure s₀'
  haveI := localColim_rel_countable s₀'
  obtain ⟨e, he⟩ := exists_ΓEMlocalEnum s₀'
  obtain ⟨b, hbPair, hbInd⟩ := hExtract (localColim s₀') e M hSize
  rw [← he] at hbInd
  set ctx : LocalEMContext (localColim s₀') J (M := M) :=
    ⟨b, ΓEMlocal s₀', hbInd.isLomega1omegaIndiscernibleOnTail,
      locDeEqAtom_mem_ΓEMlocal J s₀', locDeRelAtom_mem_ΓEMlocal J s₀'⟩ with hctx
  letI : (localColim s₀')[[J]].Structure ctx.Carrier := ctx.structure
  letI instN : (funSublang (L := L') φ.functionsIn)[[J]].Structure ctx.Carrier :=
    ((LlocalInclusion s₀' 0).addConstants J).reduct ctx.Carrier
  have hmodel := LocalEMContext.templateTheoryOn_seed_model s₀' J ctx subset_rfl
    (LocalEMContext.omegaCompleteForColim_of_indiscernibleOn s₀' J ctx subset_rfl hbInd)
  -- the two positive template facts at the sublanguage
  have hposφ : ∀ t : Fin 0 ↪o J, Sentenceω.Realize
      (Lomega1omegaTemplate.templateSentence (φ.restrictFuns (subset_refl _)) t)
      ctx.Carrier :=
    fun t => hmodel _ ⟨0, φ.restrictFuns (subset_refl _), t, ⟨0, rfl⟩,
      Or.inl ⟨(tailTemplateOfSeq_truth_sentence_iff b _).mpr hφ₀real, rfl⟩⟩
  have hposd : ∀ t : Fin 2 ↪o J, Sentenceω.Realize
      (Lomega1omegaTemplate.templateSentence
        (disEqFormula : (funSublang (L := L') φ.functionsIn).BoundedFormulaω Empty 2) t)
      ctx.Carrier :=
    fun t => hmodel _ ⟨2, disEqFormula, t, ⟨1, rfl⟩,
      Or.inl ⟨tailTemplateOfSeq_truth_disEq hbPair, rfl⟩⟩
  -- nonempty carrier (a skeleton class), expansion, and the member-wise model
  haveI : Nonempty ctx.Carrier := ⟨ctx.mkClass (t := Term.func
    (Sum.inr (Classical.arbitrary J) : (localColim s₀')[[J]].Functions 0) Fin.elim0)⟩
  letI instE : L'[[J]].Structure ctx.Carrier := expandFunStructure φ.functionsIn J
  refine ⟨ctx.Carrier, instE, ?_⟩
  rintro σ ⟨n, ψ, t, ⟨k, hk⟩, hcase⟩
  match k, hk with
  | 0, hk =>
    cases hk
    rcases hcase with ⟨_, rfl⟩ | ⟨hnot, _⟩
    · have h := (realize_templateSentence_expand (F := φ.functionsIn) J
        (φ.restrictFuns (subset_refl _)) t).mpr (hposφ t)
      rwa [hφ₀map] at h
    · exact absurd ((tailTemplateOfSeq_truth_sentence_iff a φ).mpr hφreal) hnot
  | 1, hk =>
    cases hk
    rcases hcase with ⟨_, rfl⟩ | ⟨hnot, _⟩
    · have h := (realize_templateSentence_expand (F := φ.functionsIn) J
        (disEqFormula : (funSublang (L := L') φ.functionsIn).BoundedFormulaω Empty 2) t).mpr
        (hposd t)
      rwa [show ((disEqFormula :
          (funSublang (L := L') φ.functionsIn).BoundedFormulaω Empty 2).mapLanguage
          (funSublangIncl φ.functionsIn)) = (disEqFormula : L'.BoundedFormulaω Empty 2)
        from rfl] at h
    · exact absurd (tailTemplateOfSeq_truth_disEq hPair) hnot
  | k + 2, hk =>
    cases hk
    rcases hcase with ⟨_, rfl⟩ | ⟨hnot, _⟩
    · have h := (realize_templateSentence_expand (F := φ.functionsIn) J
        (φ.restrictFuns (subset_refl _)) t).mpr (hposφ t)
      rwa [hφ₀map] at h
    · exact absurd ((tailTemplateOfSeq_truth_sentence_iff a φ).mpr hφreal) hnot

/-- **Morley–Hanf from the classical extraction alone**: `ℶ_{ω₁}` is a Hanf bound for every
`L_{ω₁ω}` sentence over a countable-relational language, assuming only the
full-indiscernibility extraction residual `MorleyHanfExtraction` — with no extra
function-symbol countability (discharged by the generated sublanguage). The tightest endpoint
of the local EM route: extraction is the sole non-formal input — no compactness oracle, no
template-realizability oracle, no Ω-completeness. -/
theorem morley_hanf_of_morleyHanfExtraction {L' : Language.{0, 0}}
    [Countable (Σ l, L'.Relations l)]
    (hExtract : ∀ (L'' : Language.{0, 0}) [Countable (Σ l, L''.Relations l)],
      MorleyHanfExtraction (L' := L''))
    (φ : L'.Sentenceω) :
    IsHanfBound φ (Cardinal.beth (Ordinal.omega 1)) :=
  morley_hanf_of_tail_realizable
    (morleySeedTailTemplateRealizable_of_morleyHanfExtraction hExtract) φ

/-! ### Compact-free pure-coloring and Erdős–Rado endpoints

The pure-coloring headlines with **no compactness oracle** — the local EM route discharges the
model-existence side, so the sole hypothesis is the partition-calculus content. The legacy
`*_pureColoring_and_compact` wrappers in `Conditional/MorleyHanfTransfer.lean` are superseded. -/

/-- **Morley–Hanf from the pure-coloring hypothesis alone**: `ℶ_{ω₁}` is a Hanf bound for every
`L_{ω₁ω}` sentence over a countable-relational language, assuming only
`PureColoringHypothesis` — the language-free partition-calculus residual. No compactness
oracle: composes the proved chain `PureColoringHypothesis →
IndiscernibleSequenceHypothesis → MorleyHanfExtraction → Morley–Hanf` (the last arrow being the
local EM construction). -/
theorem morley_hanf_of_pureColoring {L' : Language.{0, 0}}
    [Countable (Σ l, L'.Relations l)]
    (hPure : PureColoringHypothesis) (φ : L'.Sentenceω) :
    IsHanfBound φ (Cardinal.beth (Ordinal.omega 1)) :=
  morley_hanf_of_morleyHanfExtraction
    (fun _ _ => morleyHanfExtraction_of_indiscernibleSequence
      (indiscernibleSequence_of_pureColoring hPure)) φ

/-- `HasArbLargeModels` form of `morley_hanf_of_pureColoring`. -/
theorem hasArbLargeModels_of_pureColoring {L' : Language.{0, 0}}
    [Countable (Σ l, L'.Relations l)]
    (hPure : PureColoringHypothesis) (φ : L'.Sentenceω)
    (hφ : ∃ (M : Type) (_ : L'.Structure M), Sentenceω.Realize φ M ∧
      Cardinal.mk M ≥ Cardinal.beth (Ordinal.omega 1)) :
    HasArbLargeModels φ :=
  morley_hanf_of_pureColoring hPure φ hφ

/-- **Morley–Hanf from the finite-arity Erdős–Rado statement**: the ER-facing endpoint.
`FiniteArityErdosRadoOmega1 ℶ_1` — one `ω₁`-suborder homogeneous for a per-arity coloring family
with color types of size `≤ ℶ_1` — implies the `ℶ_{ω₁}` Hanf bound, via the countable-family
packing `pureColoringHypothesis_of_finiteArityErdosRadoOmega1` and the compact-free chain above.
**The hypothesis is FALSE-SHAPED** (statement audit 2026-07-07: refutable in ZFC via the
Erdős-cardinal argument — see `PureColoringHypothesis`/`FiniteArityErdosRadoOmega1`), so this
true implication cannot be discharged. The proved combinatorial supply is the bounded
`finiteArityErdosRadoBounded` (`Combinatorics/FiniteArityErdosRadoInduction.lean`), and the
honest route to the Hanf bound is a template/consistency-property reshape of the extraction
hypothesis (Marker §5.2) — the next design chunk — not an in-`M` extraction. -/
theorem morley_hanf_of_finiteArityErdosRado {L' : Language.{0, 0}}
    [Countable (Σ l, L'.Relations l)]
    (hER : FiniteArityErdosRadoOmega1 (Cardinal.beth 1)) (φ : L'.Sentenceω) :
    IsHanfBound φ (Cardinal.beth (Ordinal.omega 1)) :=
  morley_hanf_of_pureColoring (pureColoringHypothesis_of_finiteArityErdosRadoOmega1 hER) φ

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
