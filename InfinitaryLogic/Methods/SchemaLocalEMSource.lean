/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.LocalSkolemUniversal
import InfinitaryLogic.Methods.SchemaTermTruth

/-!
# The schema term model as a local-EM source

The integration point of the schema route with the (now generic) local-EM truth-lemma chain: the
schema term model satisfies the FULL arbitrary-stage Skolem-universality mixin
`LocalSkolemUniversalForColim` — no weakening to successor stages is needed.

The subtle point is a raw-stage membership `⟨n, .all ψ⟩ ∈ Γlocal s₀ k`: the body `ψ` itself need
not lie in `Γlocal s₀ k` (stage `0` is not subformula closed), so the restricted truth lemma
cannot be applied to it directly. The route is `liftNegBody_mem_Γlocal_succ`: the lifted negated
body `(ψ.not).mapLanguage (LlocalHom s₀ k)` IS controlled one stage up. Truth of `ψ` at the
stage-`k` Skolem value (the class of `locSkWitnessTerm`) makes the lifted negated body false in
the quotient; completeness pins its negation in the completion; and if the universal sentence
were negative, one two-sentence Marker body would realize both signs — under the body's
interpretation, `locSkWitness_universal_constInterp_nat` turns the first fact into the universal,
a contradiction. The universal sentence is therefore positive, and the truth lemma reads it back
into the quotient.
-/

namespace FirstOrder.Language

open Cardinal

variable {s₀ : LocalStage} {M : Type} [s₀.Lang.Structure M]
  [Nonempty M] [LinearOrder M] [WellFoundedLT M]

set_option maxHeartbeats 1000000 in
/-- **The schema term model satisfies the Skolem-universality mixin** — the full arbitrary-stage
form. This is what plugs the schema term model into the generic local-EM truth lemma
(`truthLemmaStage_of_skolemUniversal`) and the cross-source acceptance. -/
theorem schemaTerm_localSkolemUniversalForColim
    (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M) :
    letI : (localColim s₀).Structure M := localColimStructure s₀
    letI : (localColim s₀)[[ℕ]].Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
      schemaTermStructure hM
    letI : (localColim s₀).Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
      (lhomWithConstants (localColim s₀) ℕ).reduct _
    LocalSkolemUniversalForColim s₀ (M := SchemaTermCarrier (s₀ := s₀) (M := M) hM) := by
  letI : (localColim s₀).Structure M := localColimStructure s₀
  letI : (localColim s₀)[[ℕ]].Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    schemaTermStructure hM
  letI : (localColim s₀).Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    (lhomWithConstants (localColim s₀) ℕ).reduct _
  haveI : (lhomWithConstants (localColim s₀) ℕ).IsExpansionOn
      (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    LHom.isExpansionOn_reduct _ _
  refine ⟨?_⟩
  intro k n ψ h xs hψw
  classical
  let ts : Fin n → (localColim s₀)[[ℕ]].Term Empty := fun i => Quotient.out (xs i)
  have hxs : (fun i => SchemaTermCarrier.mk hM (ts i)) = xs := by
    funext i
    exact Quotient.out_eq (xs i)
  have hwval : Structure.funMap
        ((LlocalInclusion s₀ (k + 1)).onFunction
          (Sum.inr (skolemNeedSymbol h) : (Llocal s₀ (k + 1)).Functions n)) xs
      = SchemaTermCarrier.mk hM (locSkWitnessTerm s₀ ℕ h ts) := by
    rw [← hxs]
    change @Structure.funMap ((localColim s₀)[[ℕ]])
        (SchemaTermCarrier (s₀ := s₀) (M := M) hM) (schemaTermStructure hM) n
        ((lhomWithConstants (localColim s₀) ℕ).onFunction
          ((LlocalInclusion s₀ (k + 1)).onFunction
            (Sum.inr (skolemNeedSymbol h) : (Llocal s₀ (k + 1)).Functions n)))
        (fun i => SchemaTermCarrier.mk hM (ts i)) = _
    rw [schemaTerm_funMap_mk hM]
    rfl
  have hsnoc : Fin.snoc xs
        (Structure.funMap
          ((LlocalInclusion s₀ (k + 1)).onFunction
            (Sum.inr (skolemNeedSymbol h) : (Llocal s₀ (k + 1)).Functions n)) xs)
      = fun i => SchemaTermCarrier.mk hM
          ((Fin.snoc ts (locSkWitnessTerm s₀ ℕ h ts) :
            Fin (n + 1) → (localColim s₀)[[ℕ]].Term Empty) i) := by
    rw [hwval, ← hxs]
    exact (Fin.comp_snoc (SchemaTermCarrier.mk hM) ts (locSkWitnessTerm s₀ ℕ h ts)).symm
  rw [hsnoc] at hψw
  let negBody : (Llocal s₀ (k + 1)).BoundedFormulaω Empty (n + 1) :=
    (ψ.not).mapLanguage (LlocalHom s₀ k)
  let args : Fin (n + 1) → (localColim s₀)[[ℕ]].Term Empty :=
    Fin.snoc ts (locSkWitnessTerm s₀ ℕ h ts)
  have hnegmem : (⟨n + 1, negBody⟩ : Σ n, (Llocal s₀ (k + 1)).BoundedFormulaω Empty n)
      ∈ Γlocal s₀ (k + 1) := liftNegBody_mem_Γlocal_succ s₀ h
  have hneg_not_mem :
      schemaFormulaSentence (negBody.mapLanguage (LlocalInclusion s₀ (k + 1))) args
        ∉ schemaCompletionTheory (schemaEnumeration s₀) hM := by
    intro hnegT
    have hnegReal := (schemaTruthLemmaStage hM k negBody hnegmem args).mpr hnegT
    have hnegBase : (negBody.mapLanguage (LlocalInclusion s₀ (k + 1))).Realize
        (Empty.elim : Empty → SchemaTermCarrier (s₀ := s₀) (M := M) hM)
        (fun i => SchemaTermCarrier.mk hM (args i)) :=
      (BoundedFormulaω.realize_mapLanguage (lhomWithConstants (localColim s₀) ℕ)
        (negBody.mapLanguage (LlocalInclusion s₀ (k + 1)))
        (Empty.elim : Empty → SchemaTermCarrier (s₀ := s₀) (M := M) hM)
        (fun i => SchemaTermCarrier.mk hM (args i))).mp hnegReal
    change (((ψ.not).mapLanguage (LlocalHom s₀ k)).mapLanguage
        (LlocalInclusion s₀ (k + 1))).Realize _ _ at hnegBase
    rw [mapLanguage_LlocalInclusion_lift, BoundedFormulaω.mapLanguage_not,
      BoundedFormulaω.realize_not] at hnegBase
    exact hnegBase hψw
  have hneg_not_T :
      (schemaFormulaSentence (negBody.mapLanguage (LlocalInclusion s₀ (k + 1))) args).not
        ∈ schemaCompletionTheory (schemaEnumeration s₀) hM :=
    (schemaCompletionTheory_not_mem_iff hM _
      (schemaFormulaSentence_mem_universe
        (toLocalColimFormula_mem_ΓlocalColim s₀ hnegmem) args)).mpr hneg_not_mem
  have hAllT :
      schemaFormulaSentence ((BoundedFormulaω.all ψ).mapLanguage (LlocalInclusion s₀ k)) ts
        ∈ schemaCompletionTheory (schemaEnumeration s₀) hM := by
    rcases (schemaCompletionTheorySpec hM).complete_on_universe _
      (schemaFormulaSentence_mem_universe
        (toLocalColimFormula_mem_ΓlocalColim s₀ h) ts) with hpos | hneg
    · exact hpos
    · exfalso
      obtain ⟨σ, w', hbody⟩ := exists_body_of_subset hM
        {(schemaFormulaSentence (negBody.mapLanguage (LlocalInclusion s₀ (k + 1))) args).not,
          (schemaFormulaSentence
            ((BoundedFormulaω.all ψ).mapLanguage (LlocalInclusion s₀ k)) ts).not}
        (fun τ hτ => by
          rw [Finset.mem_insert, Finset.mem_singleton] at hτ
          rcases hτ with rfl | rfl
          · exact hneg_not_T
          · exact hneg)
      have h1 := hbody _ (Finset.mem_insert_self _ _)
      have h2 := hbody _
        (by rw [Finset.mem_insert]
            exact Or.inr (Finset.mem_singleton_self _))
      rw [realizeWith_not, realize_schemaFormulaSentence_iff] at h1 h2
      change ¬ (((ψ.not).mapLanguage (LlocalHom s₀ k)).mapLanguage
        (LlocalInclusion s₀ (k + 1))).Realize _ _ at h1
      rw [mapLanguage_LlocalInclusion_lift, BoundedFormulaω.mapLanguage_not,
        BoundedFormulaω.realize_not] at h1
      letI : (constantsOn ℕ).Structure M := constantsOn.structure σ
      have hψσ : (ψ.mapLanguage (LlocalInclusion s₀ k)).Realize (Empty.elim : Empty → M)
          (fun i => (args i).realize Empty.elim) := Classical.not_not.mp h1
      refine h2 ?_
      intro x
      refine locSkWitness_universal_constInterp_nat s₀ σ h ts ?_ x
      rw [show (Fin.snoc (fun i => (ts i).realize Empty.elim)
            ((locSkWitnessTerm s₀ ℕ h ts).realize Empty.elim) : Fin (n + 1) → M)
          = fun i => (args i).realize Empty.elim from
        (Fin.comp_snoc
          (fun t : (localColim s₀)[[ℕ]].Term Empty => t.realize (Empty.elim : Empty → M))
          ts (locSkWitnessTerm s₀ ℕ h ts)).symm]
      exact hψσ
  have hall := (schemaTruthLemmaStage_of_mem hM k (BoundedFormulaω.all ψ) h ts).mpr hAllT
  have hallBase : ((BoundedFormulaω.all ψ).mapLanguage (LlocalInclusion s₀ k)).Realize
      (Empty.elim : Empty → SchemaTermCarrier (s₀ := s₀) (M := M) hM)
      (fun i => SchemaTermCarrier.mk hM (ts i)) :=
    (BoundedFormulaω.realize_mapLanguage (lhomWithConstants (localColim s₀) ℕ)
      ((BoundedFormulaω.all ψ).mapLanguage (LlocalInclusion s₀ k))
      (Empty.elim : Empty → SchemaTermCarrier (s₀ := s₀) (M := M) hM)
      (fun i => SchemaTermCarrier.mk hM (ts i))).mp hall
  rw [show ((BoundedFormulaω.all ψ).mapLanguage (LlocalInclusion s₀ k))
      = BoundedFormulaω.all (ψ.mapLanguage (LlocalInclusion s₀ k)) from rfl,
    BoundedFormulaω.realize_all] at hallBase
  intro x
  have hx := hallBase x
  rw [hxs] at hx
  exact hx

end FirstOrder.Language
