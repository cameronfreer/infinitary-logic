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

end FirstOrder.Language
