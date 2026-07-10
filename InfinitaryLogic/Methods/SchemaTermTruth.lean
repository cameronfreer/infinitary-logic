/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.SchemaTermModel

/-!
# Layer 7b, checkpoint 5b-3: the restricted schema truth lemma

The truth lemma for the schema term model (`SchemaTermCarrier`/`schemaTermStructure`): realization
of a staged-family formula in the quotient, on the classes of closed terms, is equivalent to
membership of its `schemaFormulaSentence` in the completed theory `Tσ`. Restricted — the induction
runs over the staged family `Γlocal s₀ (k+1)` (the `LocalEMContext.truthLemmaStage` organization),
never over arbitrary formulas.

This file opens with the **`all`-case input**: `locSkWitness_universal_constInterp_nat`, the
σ-generalization of `locSkWitness_universal` from the deep interpretations `locDeepInterp` to an
arbitrary constant interpretation `σ : ℕ → M` (the shape a Marker certificate body supplies). The
proof is the same contrapositive Hilbert-choice argument — `localSkolem_funMap_spec` needs no
tuple-shape hypothesis, so nothing about `σ` is used beyond interpreting the argument terms.
-/

namespace FirstOrder.Language

open Cardinal

/-! ## The `all`-case Skolem input -/

/-- **Arbitrary-constant local Skolem-witness universality**: under any constant interpretation
`σ : ℕ → M` of the sequence constants, if the body `ψ` of a staged universal `∀ψ ∈ Γlocal s₀ k`
holds at the `σ`-value of its Skolem-witness term, it holds at every `M`-element. Generalizes
`locSkWitness_universal` from the deep tuples `locDeepInterp` to the interpretations a Marker
certificate body supplies. -/
theorem locSkWitness_universal_constInterp_nat
    (s₀ : LocalStage) {M : Type} [s₀.Lang.Structure M] [Nonempty M]
    (σ : ℕ → M) {k n : ℕ}
    {ψ : (Llocal s₀ k).BoundedFormulaω Empty (n + 1)}
    (h : (⟨n, .all ψ⟩ : Σ n, (Llocal s₀ k).BoundedFormulaω Empty n) ∈ Γlocal s₀ k)
    (ts : Fin n → (localColim s₀)[[ℕ]].Term Empty) :
    letI : (localColim s₀).Structure M := localColimStructure s₀
    letI : (constantsOn ℕ).Structure M := constantsOn.structure σ
    (ψ.mapLanguage (LlocalInclusion s₀ k)).Realize (Empty.elim : Empty → M)
        (Fin.snoc (fun i => (ts i).realize (Empty.elim : Empty → M))
          ((locSkWitnessTerm s₀ ℕ h ts).realize (Empty.elim : Empty → M))) →
      ∀ x : M,
        (ψ.mapLanguage (LlocalInclusion s₀ k)).Realize (Empty.elim : Empty → M)
          (Fin.snoc (fun i => (ts i).realize (Empty.elim : Empty → M)) x) := by
  letI : (localColim s₀).Structure M := localColimStructure s₀
  letI : (Llocal s₀ k).Structure M := localStageStructure s₀ k
  letI : (constantsOn ℕ).Structure M := constantsOn.structure σ
  simp only [realize_map_LlocalInclusion]
  intro hψw x
  by_contra hcon
  have hex : ∃ b, (ψ.not).Realize (Empty.elim : Empty → M)
      (Fin.snoc (fun i => (ts i).realize (Empty.elim : Empty → M)) b) :=
    ⟨x, by rw [BoundedFormulaω.realize_not]; exact hcon⟩
  have hspec : (ψ.not).Realize (Empty.elim : Empty → M)
      (Fin.snoc (fun i => (ts i).realize (Empty.elim : Empty → M))
        (Structure.funMap
          (L := localSkolem (Llocal s₀ k) (skolemNeed (Γlocal s₀ k)))
          (skolemNeedSymbol h) (fun i => (ts i).realize (Empty.elim : Empty → M)))) :=
    localSkolem_funMap_spec (skolemNeedSymbol h) _ hex
  rw [show Structure.funMap
        (L := localSkolem (Llocal s₀ k) (skolemNeed (Γlocal s₀ k)))
        (skolemNeedSymbol h) (fun i => (ts i).realize (Empty.elim : Empty → M))
      = (locSkWitnessTerm s₀ ℕ h ts).realize (Empty.elim : Empty → M) by
        rw [locSkWitnessTerm, Term.realize_func]
        rfl,
    BoundedFormulaω.realize_not] at hspec
  exact hspec hψw

/-! ## The truth-lemma helper layer

Three small bridges the induction consumes at every case: the sign flip on universe members
(negation membership ↔ non-membership), the carrier term bridge (open terms realized at classes
are classes of closed substitution instances), and the substitution/valuation exchange for closed
instances in an arbitrary structure. -/

section Helpers

variable {s₀ : LocalStage} {M : Type} [(localColim s₀).Structure M] [LinearOrder M]
  [WellFoundedLT M] (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M)

/-- **Sign flip on the universe.** For a universe member, the completed theory contains its
negation iff it does not contain the sentence itself (forward: a two-element fragment of `Tσ`
would be a consistent set containing a sentence and its negation; backward: completeness). -/
theorem schemaCompletionTheory_not_mem_iff
    (τ : FSentence (L'' := localColim s₀) (J := ℕ)) (hτ : τ ∈ schemaFSentenceUniverse s₀) :
    τ.1.not ∈ schemaCompletionTheory (schemaEnumeration s₀) hM ↔
      τ.1 ∉ schemaCompletionTheory (schemaEnumeration s₀) hM := by
  classical
  constructor
  · intro hneg hpos
    refine markerHenkinConsistent_not_mem_and_not_mem
      ((schemaCompletionTheorySpec hM).finite_consistent {τ.1, τ.1.not} fun τ' hτ' => ?_) τ.1
      ⟨Finset.mem_insert_self _ _, by
        rw [Finset.mem_insert]; exact Or.inr (Finset.mem_singleton_self _)⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hτ'
    rcases hτ' with rfl | rfl
    · exact hpos
    · exact hneg
  · intro hnot
    rcases (schemaCompletionTheorySpec hM).complete_on_universe τ hτ with hpos | hneg
    · exact absurd hpos hnot
    · exact hneg

/-- **The carrier term bridge**: an open `(localColim s₀)[[ℕ]]`-term realized in the schema term
model at class-valued variables is the class of its closed substitution instance. -/
theorem schemaTerm_realize_sumElim_mk {n : ℕ}
    (u : (localColim s₀)[[ℕ]].Term (Empty ⊕ Fin n))
    (ts : Fin n → (localColim s₀)[[ℕ]].Term Empty) :
    letI := schemaTermStructure (s₀ := s₀) (M := M) hM
    u.realize (Sum.elim (Empty.elim : Empty → SchemaTermCarrier (s₀ := s₀) (M := M) hM)
        fun i => SchemaTermCarrier.mk hM (ts i))
      = SchemaTermCarrier.mk hM (u.subst (Sum.elim (fun e => e.elim) ts)) := by
  letI := schemaTermStructure (s₀ := s₀) (M := M) hM
  induction u with
  | var x =>
    rcases x with e | i
    · exact e.elim
    · rfl
  | func f us ih =>
    show Structure.funMap f _ = _
    rw [funext ih]
    exact schemaTerm_funMap_mk hM f _

omit [(localColim s₀).Structure M] [LinearOrder M] [WellFoundedLT M] in
/-- **Substitution/valuation exchange**: a closed substitution instance realizes (in any
structure) to the open term realized at the values of the substituted terms. -/
theorem realize_subst_sumElim {N : Type} [(localColim s₀)[[ℕ]].Structure N] {n : ℕ}
    (u : (localColim s₀)[[ℕ]].Term (Empty ⊕ Fin n))
    (ts : Fin n → (localColim s₀)[[ℕ]].Term Empty) :
    (u.subst (Sum.elim (fun e => e.elim) ts)).realize (Empty.elim : Empty → N)
      = u.realize (Sum.elim (Empty.elim : Empty → N) fun i => (ts i).realize Empty.elim) := by
  rw [Term.realize_subst]
  congr 1
  funext x
  rcases x with e | i
  · exact e.elim
  · rfl

end Helpers

/-! ## The staged restricted truth lemma -/

section StagedTruthLemma

variable {s₀ : LocalStage} {M : Type} [s₀.Lang.Structure M] [Nonempty M] [LinearOrder M]
  [WellFoundedLT M]

set_option maxHeartbeats 1000000 in
/-- **The staged restricted schema truth lemma.** For a successor-stage family formula
`ψ ∈ Γlocal s₀ (k + 1)` and closed argument terms `ts`, realizing the colimit image of `ψ` in the
schema term model on the classes of `ts` is equivalent to membership of its
`schemaFormulaSentence` in the completed theory `Tσ`. The source `M` carries the CANONICAL
`localColimStructure` (the `all` case consumes the Hilbert-choice Skolem interpretations via
`locSkWitness_universal_constInterp_nat`). Modeled on `LocalEMContext.truthLemmaStage`: the
induction threads the family membership; atoms normalize to the 5a atomic API through the carrier
term bridge and semantic sign transport; `imp` is propositional completeness; `iSup`/`iInf`
consume the canonical-deForm connective witnesses (5b-2) — the negative `iInf` direction is
exactly what the completion repair pinned; `all` runs the Skolem-witness argument against a
certificate body. (The heartbeat bump is for the seven-case induction as a single elaboration
unit; no individual step is deep.) -/
theorem schemaTruthLemmaStage :
    letI : (localColim s₀).Structure M := localColimStructure s₀
    ∀ (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M)
      (k : ℕ) {n : ℕ} (ψ : (Llocal s₀ (k + 1)).BoundedFormulaω Empty n),
      (⟨n, ψ⟩ : Σ n, (Llocal s₀ (k + 1)).BoundedFormulaω Empty n) ∈ Γlocal s₀ (k + 1) →
      ∀ ts : Fin n → (localColim s₀)[[ℕ]].Term Empty,
        (@BoundedFormulaω.Realize ((localColim s₀)[[ℕ]])
            (SchemaTermCarrier (s₀ := s₀) (M := M) hM) (schemaTermStructure hM) Empty n
            ((ψ.mapLanguage (LlocalInclusion s₀ (k + 1))).mapLanguage
              (lhomWithConstants (localColim s₀) ℕ))
            (Empty.elim : Empty → SchemaTermCarrier (s₀ := s₀) (M := M) hM)
            (fun i => SchemaTermCarrier.mk hM (ts i)) ↔
          schemaFormulaSentence (ψ.mapLanguage (LlocalInclusion s₀ (k + 1))) ts
            ∈ schemaCompletionTheory (schemaEnumeration s₀) hM) := by
  letI : (localColim s₀).Structure M := localColimStructure s₀
  intro hM k
  letI := schemaTermStructure (s₀ := s₀) (M := M) hM
  intro n ψ
  induction ψ with
  | falsum =>
    intro _ ts
    simp only [BoundedFormulaω.mapLanguage, BoundedFormulaω.realize_falsum, false_iff]
    intro hT
    obtain ⟨σ, w, hbody⟩ := exists_body_of_subset hM
      {schemaFormulaSentence (BoundedFormulaω.falsum.mapLanguage (LlocalInclusion s₀ (k + 1))) ts}
      (fun τ hτ => by rw [Finset.mem_singleton] at hτ; exact hτ ▸ hT)
    have hf := hbody _ (Finset.mem_singleton_self _)
    rw [realize_schemaFormulaSentence_iff] at hf
    exact hf
  | equal t₁ t₂ =>
    intro hmem ts
    rw [show ((BoundedFormulaω.equal t₁ t₂).mapLanguage (LlocalInclusion s₀ (k + 1))).mapLanguage
          (lhomWithConstants (localColim s₀) ℕ)
        = BoundedFormulaω.equal
            ((lhomWithConstants (localColim s₀) ℕ).onTerm
              ((LlocalInclusion s₀ (k + 1)).onTerm t₁))
            ((lhomWithConstants (localColim s₀) ℕ).onTerm
              ((LlocalInclusion s₀ (k + 1)).onTerm t₂)) from rfl,
      BoundedFormulaω.realize_equal, schemaTerm_realize_sumElim_mk hM _ ts,
      schemaTerm_realize_sumElim_mk hM _ ts, SchemaTermCarrier.mk_eq_mk_iff hM]
    refine schema_mem_iff_of_semantic_iff hM
      (locDeEqAtom_mem_ΓEMlocal (J := ℕ) (s₀ := s₀) (S := schemaSupport _ _) _ _
        Finset.subset_union_left Finset.subset_union_right)
      ((schemaSupport _ _).orderEmbOfFin rfl)
      (locDeForm_mem_ΓEMlocal ℕ s₀ (schemaRelSupport ts)
        (toLocalColimFormula_mem_ΓlocalColim s₀ hmem) ts
        (locJSupport_subset_schemaRelSupport ts))
      ((schemaRelSupport ts).orderEmbOfFin rfl)
      (fun σ w => ?_)
    letI : (constantsOn ℕ).Structure M := constantsOn.structure σ
    have mid : ((((lhomWithConstants (localColim s₀) ℕ).onTerm
            ((LlocalInclusion s₀ (k + 1)).onTerm t₁)).subst
              (Sum.elim (fun e => e.elim) ts)).realize (Empty.elim : Empty → M)
          = (((lhomWithConstants (localColim s₀) ℕ).onTerm
            ((LlocalInclusion s₀ (k + 1)).onTerm t₂)).subst
              (Sum.elim (fun e => e.elim) ts)).realize (Empty.elim : Empty → M))
        ↔ ((BoundedFormulaω.equal t₁ t₂).mapLanguage (LlocalInclusion s₀ (k + 1))).Realize
            (Empty.elim : Empty → M) (fun i => (ts i).realize Empty.elim) := by
      rw [show (BoundedFormulaω.equal t₁ t₂).mapLanguage (LlocalInclusion s₀ (k + 1))
          = BoundedFormulaω.equal ((LlocalInclusion s₀ (k + 1)).onTerm t₁)
              ((LlocalInclusion s₀ (k + 1)).onTerm t₂) from rfl,
        BoundedFormulaω.realize_equal, realize_subst_sumElim, realize_subst_sumElim,
        LHom.realize_onTerm (lhomWithConstants (localColim s₀) ℕ),
        LHom.realize_onTerm (lhomWithConstants (localColim s₀) ℕ)]
    exact (realize_schemaEqSentence_iff σ w _ _).trans
      (mid.trans (realize_schemaFormulaSentence_iff σ w _ ts).symm)
  | rel R args =>
    intro hmem ts
    rw [show ((BoundedFormulaω.rel R args).mapLanguage (LlocalInclusion s₀ (k + 1))).mapLanguage
          (lhomWithConstants (localColim s₀) ℕ)
        = BoundedFormulaω.rel
            (Sum.inl ((LlocalInclusion s₀ (k + 1)).onRelation R) :
              ((localColim s₀)[[ℕ]]).Relations _)
            (fun i => (lhomWithConstants (localColim s₀) ℕ).onTerm
              ((LlocalInclusion s₀ (k + 1)).onTerm (args i))) from rfl,
      BoundedFormulaω.realize_rel]
    simp only [schemaTerm_realize_sumElim_mk hM]
    rw [schemaTerm_relMap_mk_iff hM]
    refine schema_mem_iff_of_semantic_iff hM
      (locDeRelAtom_mem_ΓEMlocal (J := ℕ) (s₀ := s₀) (S := schemaRelSupport _)
        ((LlocalInclusion s₀ (k + 1)).onRelation R) _
        (locJSupport_subset_schemaRelSupport _))
      ((schemaRelSupport _).orderEmbOfFin rfl)
      (locDeForm_mem_ΓEMlocal ℕ s₀ (schemaRelSupport ts)
        (toLocalColimFormula_mem_ΓlocalColim s₀ hmem) ts
        (locJSupport_subset_schemaRelSupport ts))
      ((schemaRelSupport ts).orderEmbOfFin rfl)
      (fun σ w => ?_)
    letI : (constantsOn ℕ).Structure M := constantsOn.structure σ
    have mid : (Structure.RelMap ((LlocalInclusion s₀ (k + 1)).onRelation R)
          fun i => (((lhomWithConstants (localColim s₀) ℕ).onTerm
              ((LlocalInclusion s₀ (k + 1)).onTerm (args i))).subst
                (Sum.elim (fun e => e.elim) ts)).realize (Empty.elim : Empty → M))
        ↔ ((BoundedFormulaω.rel R args).mapLanguage (LlocalInclusion s₀ (k + 1))).Realize
            (Empty.elim : Empty → M) (fun i => (ts i).realize Empty.elim) := by
      rw [show (BoundedFormulaω.rel R args).mapLanguage (LlocalInclusion s₀ (k + 1))
          = BoundedFormulaω.rel ((LlocalInclusion s₀ (k + 1)).onRelation R)
              (fun i => (LlocalInclusion s₀ (k + 1)).onTerm (args i)) from rfl,
        BoundedFormulaω.realize_rel]
      apply Iff.of_eq
      congr 1
      funext i
      rw [realize_subst_sumElim, LHom.realize_onTerm (lhomWithConstants (localColim s₀) ℕ)]
    exact (realize_schemaRelSentence_iff σ w _ _).trans
      (mid.trans (realize_schemaFormulaSentence_iff σ w _ ts).symm)
  | imp φ ψ' ihφ ihψ =>
    intro hmem ts
    classical
    have hφmem : (⟨_, φ⟩ : Σ n, (Llocal s₀ (k + 1)).BoundedFormulaω Empty n)
        ∈ Γlocal s₀ (k + 1) :=
      bfSubformulas_subset_Γlocal_succ s₀ hmem (Set.mem_insert _ _)
    have hψmem : (⟨_, ψ'⟩ : Σ n, (Llocal s₀ (k + 1)).BoundedFormulaω Empty n)
        ∈ Γlocal s₀ (k + 1) :=
      bfSubformulas_subset_Γlocal_succ s₀ hmem (Set.mem_insert_of_mem _ rfl)
    have hφu := schemaFormulaSentence_mem_universe
      (toLocalColimFormula_mem_ΓlocalColim s₀ hφmem) ts
    have hψu := schemaFormulaSentence_mem_universe
      (toLocalColimFormula_mem_ΓlocalColim s₀ hψmem) ts
    have himpu := schemaFormulaSentence_mem_universe
      (toLocalColimFormula_mem_ΓlocalColim s₀ hmem) ts
    rw [show ((φ.imp ψ').mapLanguage (LlocalInclusion s₀ (k + 1))).mapLanguage
          (lhomWithConstants (localColim s₀) ℕ)
        = ((φ.mapLanguage (LlocalInclusion s₀ (k + 1))).mapLanguage
            (lhomWithConstants (localColim s₀) ℕ)).imp
          ((ψ'.mapLanguage (LlocalInclusion s₀ (k + 1))).mapLanguage
            (lhomWithConstants (localColim s₀) ℕ)) from rfl,
      BoundedFormulaω.realize_imp, ihφ hφmem ts, ihψ hψmem ts]
    constructor
    · intro h
      rcases (schemaCompletionTheorySpec hM).complete_on_universe _ himpu with hpos | hneg
      · exact hpos
      · exfalso
        by_cases hφT : schemaFormulaSentence (φ.mapLanguage (LlocalInclusion s₀ (k + 1))) ts
            ∈ schemaCompletionTheory (schemaEnumeration s₀) hM
        · obtain ⟨σ, w, hbody⟩ := exists_body_of_subset hM
            {(schemaFormulaSentence ((φ.imp ψ').mapLanguage (LlocalInclusion s₀ (k + 1))) ts).not,
              schemaFormulaSentence (ψ'.mapLanguage (LlocalInclusion s₀ (k + 1))) ts}
            (fun τ hτ => by
              rw [Finset.mem_insert, Finset.mem_singleton] at hτ
              rcases hτ with rfl | rfl
              · exact hneg
              · exact h hφT)
          have h1 := hbody _ (Finset.mem_insert_self _ _)
          have h2 := hbody _
            (by rw [Finset.mem_insert]; exact Or.inr (Finset.mem_singleton_self _))
          rw [realizeWith_not, realize_schemaFormulaSentence_iff] at h1
          rw [realize_schemaFormulaSentence_iff] at h2
          exact h1 fun _ => h2
        · obtain ⟨σ, w, hbody⟩ := exists_body_of_subset hM
            {(schemaFormulaSentence ((φ.imp ψ').mapLanguage (LlocalInclusion s₀ (k + 1))) ts).not,
              (schemaFormulaSentence (φ.mapLanguage (LlocalInclusion s₀ (k + 1))) ts).not}
            (fun τ hτ => by
              rw [Finset.mem_insert, Finset.mem_singleton] at hτ
              rcases hτ with rfl | rfl
              · exact hneg
              · exact (schemaCompletionTheory_not_mem_iff hM _ hφu).mpr hφT)
          have h1 := hbody _ (Finset.mem_insert_self _ _)
          have h2 := hbody _
            (by rw [Finset.mem_insert]; exact Or.inr (Finset.mem_singleton_self _))
          rw [realizeWith_not, realize_schemaFormulaSentence_iff] at h1
          rw [realizeWith_not, realize_schemaFormulaSentence_iff] at h2
          exact h1 fun hφr => absurd hφr h2
    · intro himp hφT
      rcases (schemaCompletionTheorySpec hM).complete_on_universe _ hψu with hpos | hneg
      · exact hpos
      · exfalso
        obtain ⟨σ, w, hbody⟩ := exists_body_of_subset hM
          {schemaFormulaSentence ((φ.imp ψ').mapLanguage (LlocalInclusion s₀ (k + 1))) ts,
            schemaFormulaSentence (φ.mapLanguage (LlocalInclusion s₀ (k + 1))) ts,
            (schemaFormulaSentence (ψ'.mapLanguage (LlocalInclusion s₀ (k + 1))) ts).not}
          (fun τ hτ => by
            rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hτ
            rcases hτ with rfl | rfl | rfl
            · exact himp
            · exact hφT
            · exact hneg)
        have h1 := hbody _ (Finset.mem_insert_self _ _)
        have h2 := hbody _
          (by rw [Finset.mem_insert, Finset.mem_insert]
              exact Or.inr (Or.inl rfl))
        have h3 := hbody _
          (by rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
              exact Or.inr (Or.inr rfl))
        rw [realize_schemaFormulaSentence_iff] at h1 h2
        rw [realizeWith_not, realize_schemaFormulaSentence_iff] at h3
        exact h3 (h1 h2)
  | all ψ₀ ih =>
    intro hmem ts
    classical
    have hbodymem : (⟨_, ψ₀⟩ : Σ n, (Llocal s₀ (k + 1)).BoundedFormulaω Empty n)
        ∈ Γlocal s₀ (k + 1) :=
      bfSubformulas_subset_Γlocal_succ s₀ hmem rfl
    rw [show ((BoundedFormulaω.all ψ₀).mapLanguage (LlocalInclusion s₀ (k + 1))).mapLanguage
          (lhomWithConstants (localColim s₀) ℕ)
        = BoundedFormulaω.all ((ψ₀.mapLanguage (LlocalInclusion s₀ (k + 1))).mapLanguage
            (lhomWithConstants (localColim s₀) ℕ)) from rfl,
      BoundedFormulaω.realize_all]
    constructor
    · intro hall
      have hw := hall (SchemaTermCarrier.mk hM (locSkWitnessTerm s₀ ℕ hmem ts))
      rw [show Fin.snoc (fun i => SchemaTermCarrier.mk hM (ts i))
            (SchemaTermCarrier.mk hM (locSkWitnessTerm s₀ ℕ hmem ts))
          = fun i => SchemaTermCarrier.mk hM
              ((Fin.snoc ts (locSkWitnessTerm s₀ ℕ hmem ts) :
                Fin _ → (localColim s₀)[[ℕ]].Term Empty) i) from
          (Fin.comp_snoc (SchemaTermCarrier.mk hM) ts
            (locSkWitnessTerm s₀ ℕ hmem ts)).symm] at hw
      have hwT := (ih hbodymem (Fin.snoc ts (locSkWitnessTerm s₀ ℕ hmem ts))).mp hw
      rcases (schemaCompletionTheorySpec hM).complete_on_universe _
        (schemaFormulaSentence_mem_universe (toLocalColimFormula_mem_ΓlocalColim s₀ hmem) ts)
        with hpos | hneg
      · exact hpos
      · exfalso
        obtain ⟨σ, w', hbody⟩ := exists_body_of_subset hM
          {schemaFormulaSentence (ψ₀.mapLanguage (LlocalInclusion s₀ (k + 1)))
              (Fin.snoc ts (locSkWitnessTerm s₀ ℕ hmem ts)),
            (schemaFormulaSentence ((BoundedFormulaω.all ψ₀).mapLanguage
              (LlocalInclusion s₀ (k + 1))) ts).not}
          (fun τ hτ => by
            rw [Finset.mem_insert, Finset.mem_singleton] at hτ
            rcases hτ with rfl | rfl
            · exact hwT
            · exact hneg)
        have h1 := hbody _ (Finset.mem_insert_self _ _)
        have h2 := hbody _
          (by rw [Finset.mem_insert]; exact Or.inr (Finset.mem_singleton_self _))
        rw [realize_schemaFormulaSentence_iff] at h1
        rw [realizeWith_not, realize_schemaFormulaSentence_iff] at h2
        letI : (constantsOn ℕ).Structure M := constantsOn.structure σ
        refine h2 ?_
        intro x
        refine locSkWitness_universal_constInterp_nat s₀ σ hmem ts ?_ x
        rw [show (Fin.snoc (fun i => (ts i).realize Empty.elim)
              ((locSkWitnessTerm s₀ ℕ hmem ts).realize Empty.elim) : Fin _ → M)
            = fun i => ((Fin.snoc ts (locSkWitnessTerm s₀ ℕ hmem ts) :
                Fin _ → (localColim s₀)[[ℕ]].Term Empty) i).realize Empty.elim from
            (Fin.comp_snoc
              (fun t : (localColim s₀)[[ℕ]].Term Empty => t.realize (Empty.elim : Empty → M))
              ts (locSkWitnessTerm s₀ ℕ hmem ts)).symm]
        exact h1
    · intro hT
      refine Quotient.ind fun u => ?_
      rw [show Fin.snoc (fun i => SchemaTermCarrier.mk hM (ts i)) (SchemaTermCarrier.mk hM u)
          = fun i => SchemaTermCarrier.mk hM
              ((Fin.snoc ts u : Fin _ → (localColim s₀)[[ℕ]].Term Empty) i) from
          (Fin.comp_snoc (SchemaTermCarrier.mk hM) ts u).symm]
      refine (ih hbodymem (Fin.snoc ts u)).mpr ?_
      rcases (schemaCompletionTheorySpec hM).complete_on_universe _
        (schemaFormulaSentence_mem_universe
          (toLocalColimFormula_mem_ΓlocalColim s₀ hbodymem) (Fin.snoc ts u)) with hpos | hneg
      · exact hpos
      · exfalso
        obtain ⟨σ, w', hbody⟩ := exists_body_of_subset hM
          {schemaFormulaSentence ((BoundedFormulaω.all ψ₀).mapLanguage
              (LlocalInclusion s₀ (k + 1))) ts,
            (schemaFormulaSentence (ψ₀.mapLanguage (LlocalInclusion s₀ (k + 1)))
              (Fin.snoc ts u)).not}
          (fun τ hτ => by
            rw [Finset.mem_insert, Finset.mem_singleton] at hτ
            rcases hτ with rfl | rfl
            · exact hT
            · exact hneg)
        have h1 := hbody _ (Finset.mem_insert_self _ _)
        have h2 := hbody _
          (by rw [Finset.mem_insert]; exact Or.inr (Finset.mem_singleton_self _))
        rw [realize_schemaFormulaSentence_iff] at h1
        rw [realizeWith_not, realize_schemaFormulaSentence_iff] at h2
        letI : (constantsOn ℕ).Structure M := constantsOn.structure σ
        refine h2 ?_
        show (ψ₀.mapLanguage (LlocalInclusion s₀ (k + 1))).Realize (Empty.elim : Empty → M)
          (fun i => ((Fin.snoc ts u : Fin _ → (localColim s₀)[[ℕ]].Term Empty) i).realize
            Empty.elim)
        rw [show (fun i => ((Fin.snoc ts u : Fin _ → (localColim s₀)[[ℕ]].Term Empty) i).realize
              (Empty.elim : Empty → M))
            = (Fin.snoc (fun i => (ts i).realize Empty.elim) (u.realize Empty.elim) :
                Fin _ → M) from
            Fin.comp_snoc
              (fun t : (localColim s₀)[[ℕ]].Term Empty => t.realize (Empty.elim : Empty → M))
              ts u]
        exact h1 (u.realize (Empty.elim : Empty → M))
  | iSup φs ih =>
    intro hmem ts
    classical
    rw [show ((BoundedFormulaω.iSup φs).mapLanguage (LlocalInclusion s₀ (k + 1))).mapLanguage
          (lhomWithConstants (localColim s₀) ℕ)
        = BoundedFormulaω.iSup (fun i => ((φs i).mapLanguage
            (LlocalInclusion s₀ (k + 1))).mapLanguage
              (lhomWithConstants (localColim s₀) ℕ)) from rfl,
      BoundedFormulaω.realize_iSup]
    constructor
    · rintro ⟨i, hi⟩
      have hiT := (ih i (bfSubformulas_subset_Γlocal_succ s₀ hmem (Set.mem_range_self i)) ts).mp hi
      rcases (schemaCompletionTheorySpec hM).complete_on_universe _
        (schemaFormulaSentence_mem_universe (toLocalColimFormula_mem_ΓlocalColim s₀ hmem) ts)
        with hpos | hneg
      · exact hpos
      · exfalso
        obtain ⟨σ, w, hbody⟩ := exists_body_of_subset hM
          {schemaFormulaSentence ((φs i).mapLanguage (LlocalInclusion s₀ (k + 1))) ts,
            (schemaFormulaSentence ((BoundedFormulaω.iSup φs).mapLanguage
              (LlocalInclusion s₀ (k + 1))) ts).not}
          (fun τ hτ => by
            rw [Finset.mem_insert, Finset.mem_singleton] at hτ
            rcases hτ with rfl | rfl
            · exact hiT
            · exact hneg)
        have h1 := hbody _ (Finset.mem_insert_self _ _)
        have h2 := hbody _
          (by rw [Finset.mem_insert]; exact Or.inr (Finset.mem_singleton_self _))
        rw [realize_schemaFormulaSentence_iff] at h1
        rw [realizeWith_not, realize_schemaFormulaSentence_iff] at h2
        exact h2 ⟨i, h1⟩
    · intro hT
      obtain ⟨j, hj⟩ := schemaCompletionTheory_iSup_witness_canonDeForm hM
        (toLocalColimFormula_mem_ΓlocalColim s₀ hmem)
        (fun i => locDeTermFin (localColim s₀) ℕ (schemaRelSupport ts) (ts i)
          (locJSupport_subset_schemaRelSupport ts i))
        ((schemaRelSupport ts).orderEmbOfFin rfl) hT
      exact ⟨j, (ih j (bfSubformulas_subset_Γlocal_succ s₀ hmem (Set.mem_range_self j)) ts).mpr hj⟩
  | iInf φs ih =>
    intro hmem ts
    classical
    have hcolim : (⟨_, BoundedFormulaω.iInf fun i =>
          (φs i).mapLanguage (LlocalInclusion s₀ (k + 1))⟩ :
        Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓlocalColim s₀ :=
      toLocalColimFormula_mem_ΓlocalColim s₀ hmem
    rw [show ((BoundedFormulaω.iInf φs).mapLanguage (LlocalInclusion s₀ (k + 1))).mapLanguage
          (lhomWithConstants (localColim s₀) ℕ)
        = BoundedFormulaω.iInf (fun i => ((φs i).mapLanguage
            (LlocalInclusion s₀ (k + 1))).mapLanguage
              (lhomWithConstants (localColim s₀) ℕ)) from rfl,
      BoundedFormulaω.realize_iInf,
      show schemaFormulaSentence
            ((BoundedFormulaω.iInf φs).mapLanguage (LlocalInclusion s₀ (k + 1))) ts
          = schemaFormulaSentence (BoundedFormulaω.iInf fun i =>
              (φs i).mapLanguage (LlocalInclusion s₀ (k + 1))) ts from rfl]
    constructor
    · intro h
      rcases (schemaCompletionTheorySpec hM).complete_on_universe _
        (schemaFormulaSentence_mem_universe hcolim ts) with hpos | hneg
      · exact hpos
      · exfalso
        obtain ⟨j, hj⟩ := schemaCompletionTheory_neg_iInf_witness_canonDeForm hM hcolim
          (fun i => locDeTermFin (localColim s₀) ℕ (schemaRelSupport ts) (ts i)
            (locJSupport_subset_schemaRelSupport ts i))
          ((schemaRelSupport ts).orderEmbOfFin rfl) hneg
        have hjT := (ih j (bfSubformulas_subset_Γlocal_succ s₀ hmem (Set.mem_range_self j)) ts).mp
          (h j)
        exact (schemaCompletionTheory_not_mem_iff hM _
          (schemaFormulaSentence_mem_universe
            (toLocalColimFormula_mem_ΓlocalColim s₀
              (bfSubformulas_subset_Γlocal_succ s₀ hmem (Set.mem_range_self j))) ts)).mp hj hjT
    · intro hT j
      apply (ih j (bfSubformulas_subset_Γlocal_succ s₀ hmem (Set.mem_range_self j)) ts).mpr
      rcases (schemaCompletionTheorySpec hM).complete_on_universe _
        (schemaFormulaSentence_mem_universe
          (toLocalColimFormula_mem_ΓlocalColim s₀
            (bfSubformulas_subset_Γlocal_succ s₀ hmem (Set.mem_range_self j))) ts)
        with hpos | hneg
      · exact hpos
      · exfalso
        obtain ⟨σ, w, hbody⟩ := exists_body_of_subset hM
          {schemaFormulaSentence ((BoundedFormulaω.iInf φs).mapLanguage
              (LlocalInclusion s₀ (k + 1))) ts,
            (schemaFormulaSentence ((φs j).mapLanguage (LlocalInclusion s₀ (k + 1))) ts).not}
          (fun τ hτ => by
            rw [Finset.mem_insert, Finset.mem_singleton] at hτ
            rcases hτ with rfl | rfl
            · exact hT
            · exact hneg)
        have h1 := hbody _ (Finset.mem_insert_self _ _)
        have h2 := hbody _
          (by rw [Finset.mem_insert]; exact Or.inr (Finset.mem_singleton_self _))
        rw [realize_schemaFormulaSentence_iff] at h1
        rw [realizeWith_not, realize_schemaFormulaSentence_iff] at h2
        exact h2 (h1 j)

end StagedTruthLemma

end FirstOrder.Language
