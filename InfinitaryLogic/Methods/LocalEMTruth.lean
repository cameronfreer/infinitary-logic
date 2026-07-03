/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.LocalEMContext

/-!
# The local EM truth lemma, layer 1: Skolem-witness transport

The restricted local truth lemma's `all` case (`∀ψ`) needs, in the source model, the Hilbert-choice
witness of `¬ψ` as an actual closed term of `(localColim s₀)[[J]]`, together with the semantic
"witness universality" it delivers. This file builds exactly that transport, mirroring the
`skWitnessTerm`/`deepInterp_skWitness`/`skWitness_universal` chain of `EMTermModel.lean` but over the
**countable** local tower:

* `locSkWitnessTerm` — the colimit-level witness term for a stage-`k` universal `∀ψ ∈ Γlocal s₀ k`,
  built from the local Skolem symbol `skolemNeedSymbol h` (witnessing `∃ xₙ, ¬ψ`), included through
  `LlocalInclusion s₀ (k+1)` and then `lhomWithConstants`;
* `locJSupport_locSkWitnessTerm` — its head is an `L`-function symbol, not a `J`-constant, so its
  `J`-support is just the union of the arguments';
* `locDeepInterp_skWitness` — its deep interpretation is exactly the Hilbert-choice value for `¬ψ`
  on the deep interpretations of the arguments (the `localColimStructure`/`localStageStructure`/
  `localSkolemStructure` funMap coherence is fully definitional, so this is `rfl` after unfolding);
* `locSkWitness_universal` — the Skolem-axiom transport: if `ψ` holds at the deep tuple extended by
  the witness's deep value, then it holds at *every* `M`-element. Powered by `localSkolem_funMap_spec`
  (in `LocalSkolem.lean`) and the realization transport `realize_map_LlocalInclusion`.

This is the local analogue of `EMTermModel.lean:114–180`. It is a pure file (imports
`LocalEMContext`, not the Conditional-touching `LocalEMExtraction`) so the local context/truth stack
stays off the EM stack.
-/

namespace FirstOrder.Language

variable (s₀ : LocalStage) (J : Type) [LinearOrder J]

/-- The **colimit-level local Skolem-witness term** for a stage-`k` universal `∀ψ ∈ Γlocal s₀ k`:
the local Skolem symbol `skolemNeedSymbol h` (witnessing `∃ xₙ, ¬ψ`), in the `localSkolem` summand of
`Llocal s₀ (k+1)`, included through `LlocalInclusion s₀ (k+1)` and then `lhomWithConstants`, applied
to the closed argument terms `ts`. Local analogue of `skWitnessTerm`. -/
def locSkWitnessTerm {k n : ℕ} {ψ : (Llocal s₀ k).BoundedFormulaω Empty (n + 1)}
    (h : (⟨n, .all ψ⟩ : Σ n, (Llocal s₀ k).BoundedFormulaω Empty n) ∈ Γlocal s₀ k)
    (ts : Fin n → (localColim s₀)[[J]].Term Empty) : (localColim s₀)[[J]].Term Empty :=
  Term.func ((lhomWithConstants (localColim s₀) J).onFunction
    ((LlocalInclusion s₀ (k + 1)).onFunction
      (Sum.inr (skolemNeedSymbol h) : (Llocal s₀ (k + 1)).Functions n))) ts

/-- The witness term mentions only the `J`-constants of its arguments (its head is an
`L`-function symbol, not a skeleton constant), so its support is covered whenever the arguments' is.
Local analogue of `jSupport_skWitnessTerm`. -/
theorem locJSupport_locSkWitnessTerm {k n : ℕ}
    {ψ : (Llocal s₀ k).BoundedFormulaω Empty (n + 1)}
    (h : (⟨n, .all ψ⟩ : Σ n, (Llocal s₀ k).BoundedFormulaω Empty n) ∈ Γlocal s₀ k)
    (ts : Fin n → (localColim s₀)[[J]].Term Empty) :
    locJSupport (localColim s₀) J (locSkWitnessTerm s₀ J h ts)
      = Finset.univ.biUnion fun i => locJSupport (localColim s₀) J (ts i) := by
  have hjc : locJConstOf (localColim s₀) J ((lhomWithConstants (localColim s₀) J).onFunction
      ((LlocalInclusion s₀ (k + 1)).onFunction (Sum.inr (skolemNeedSymbol h)))) = ∅ := by
    cases n <;> rfl
  rw [locSkWitnessTerm,
    show locJSupport (localColim s₀) J
        (Term.func ((lhomWithConstants (localColim s₀) J).onFunction
          ((LlocalInclusion s₀ (k + 1)).onFunction (Sum.inr (skolemNeedSymbol h)))) ts)
      = (Finset.univ.biUnion fun i => locJSupport (localColim s₀) J (ts i))
        ∪ locJConstOf (localColim s₀) J ((lhomWithConstants (localColim s₀) J).onFunction
            ((LlocalInclusion s₀ (k + 1)).onFunction (Sum.inr (skolemNeedSymbol h)))) from rfl,
    hjc, Finset.union_empty]

section Semantic

variable {M : Type} [s₀.Lang.Structure M] [Nonempty M] (a : ℕ → M)

/-- **Deep value of the local Skolem-witness term**: it is exactly the Hilbert-choice value for `¬ψ`
on the deep interpretations of the arguments (read in the source model's stage-`k` structure). The
`localColimStructure`/`localStageStructure`/`localSkolemStructure` funMap coherence is fully
definitional, so this is `rfl` after the term/funMap unfolding. Local analogue of
`deepInterp_skWitness`. -/
theorem locDeepInterp_skWitness (d : ℕ) (S : Finset J) {k n : ℕ}
    {ψ : (Llocal s₀ k).BoundedFormulaω Empty (n + 1)}
    (h : (⟨n, .all ψ⟩ : Σ n, (Llocal s₀ k).BoundedFormulaω Empty n) ∈ Γlocal s₀ k)
    (ts : Fin n → (localColim s₀)[[J]].Term Empty) :
    letI : (Llocal s₀ k).Structure M := localStageStructure s₀ k
    letI : (localColim s₀).Structure M := localColimStructure s₀
    locDeepInterp (localColim s₀) J a d S (locSkWitnessTerm s₀ J h ts)
      = Classical.epsilon (fun b => ψ.not.Realize (Empty.elim : Empty → M)
          (Fin.snoc (fun i => locDeepInterp (localColim s₀) J a d S (ts i)) b)) := by
  letI : (Llocal s₀ k).Structure M := localStageStructure s₀ k
  letI : (localColim s₀).Structure M := localColimStructure s₀
  rw [locSkWitnessTerm, locDeepInterp_func]; rfl

/-- **Local Skolem-witness universality** (the contrapositive Skolem axiom, transported to the deep
tuple): if the body `ψ` holds at the deep interpretation of its Skolem-witness term (for `¬ψ`), then
it holds at *every* `M`-element. The Skolem input consumed inline by the `all` case of the local
truth lemma. Local analogue of `skWitness_universal`. -/
theorem locSkWitness_universal (d : ℕ) (S : Finset J) {k n : ℕ}
    {ψ : (Llocal s₀ k).BoundedFormulaω Empty (n + 1)}
    (h : (⟨n, .all ψ⟩ : Σ n, (Llocal s₀ k).BoundedFormulaω Empty n) ∈ Γlocal s₀ k)
    (ts : Fin n → (localColim s₀)[[J]].Term Empty) :
    letI : (localColim s₀).Structure M := localColimStructure s₀
    (ψ.mapLanguage (LlocalInclusion s₀ k)).Realize (Empty.elim : Empty → M)
        (Fin.snoc (fun i => locDeepInterp (localColim s₀) J a d S (ts i))
          (locDeepInterp (localColim s₀) J a d S (locSkWitnessTerm s₀ J h ts))) →
      ∀ x : M, (ψ.mapLanguage (LlocalInclusion s₀ k)).Realize (Empty.elim : Empty → M)
          (Fin.snoc (fun i => locDeepInterp (localColim s₀) J a d S (ts i)) x) := by
  letI : (localColim s₀).Structure M := localColimStructure s₀
  letI : (Llocal s₀ k).Structure M := localStageStructure s₀ k
  simp only [realize_map_LlocalInclusion]
  intro hψw x
  by_contra hcon
  have hex : ∃ b, (ψ.not).Realize (Empty.elim : Empty → M)
      (Fin.snoc (fun i => locDeepInterp (localColim s₀) J a d S (ts i)) b) :=
    ⟨x, by rw [BoundedFormulaω.realize_not]; exact hcon⟩
  have hspec : (ψ.not).Realize (Empty.elim : Empty → M)
      (Fin.snoc (fun i => locDeepInterp (localColim s₀) J a d S (ts i))
        (Structure.funMap (L := localSkolem (Llocal s₀ k) (skolemNeed (Γlocal s₀ k)))
          (skolemNeedSymbol h) (fun i => locDeepInterp (localColim s₀) J a d S (ts i)))) :=
    localSkolem_funMap_spec (skolemNeedSymbol h) _ hex
  rw [show Structure.funMap (L := localSkolem (Llocal s₀ k) (skolemNeed (Γlocal s₀ k)))
        (skolemNeedSymbol h) (fun i => locDeepInterp (localColim s₀) J a d S (ts i))
      = locDeepInterp (localColim s₀) J a d S (locSkWitnessTerm s₀ J h ts) from
      (locDeepInterp_skWitness s₀ J a d S h ts).symm,
    BoundedFormulaω.realize_not] at hspec
  exact hspec hψw

end Semantic

end FirstOrder.Language
