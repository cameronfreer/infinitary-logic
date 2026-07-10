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

end FirstOrder.Language
