/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.SchemaOmegaWitness
import InfinitaryLogic.Methods.MarkerStage

/-!
# Layer 7b, checkpoint 1: the countable schema sentence universe

The ω-stage Henkin/template completion (Layer 7) is carried out at the **schema level**, over
the canonical countable index `J := ℕ` (the indiscernible-sequence positions `d₀, d₁, …`), where
the sentence set the completion ranges over is genuinely countable — unlike the uncountable
`L'[[J]]`-constant instances for arbitrary `J` that defeated the Layer-6c Zorn maximal.

This file fixes the **schema sentence universe**: the set of `(localColim s₀)[[ℕ]]`-sentences the
enumeration in checkpoint 3 will decide. A crucial simplification, established in
`SchemaOmegaWitness`, drives the shape: the target witness property
`TailTemplateOmegaWitnessed`/`OmegaCompleteForColim` has **only `iSup`/`iInf` clauses, no
existential** (the local-EM de-substituted formulas are already Skolemized). Since `ΓlocalColim`
— hence `ΓEMlocal` — is closed under `iSup`/`iInf` components
(`iSup_component_mem_ΓlocalColim`), every disjunct a completion might choose as a witness is
**already** a member of the seed family. So the universe is exactly the `templateSentence`
instantiations of the `ΓEMlocal` members at `ℕ`-tuples:

* the seed family `ΓEMlocal s₀` is **countable** (`ΓEMlocal_countable`);
* for each member `⟨m, φ⟩`, the increasing `ℕ`-tuples `t : Fin m ↪o ℕ` form a **countable** type
  (they inject into `Fin m → ℕ`);
* `templateSentence φ t` is the `L[[ℕ]]`-sentence "`φ` holds on `d_{t 0}, …, d_{t (m-1)}`".

`schemaSentenceUniverse_countable` is the checkpoint-1 payoff (the completion's decision list is
enumerable); `schemaSentenceUniverse_nonempty` supplies the base point the enumeration needs.
No completion, Zorn, term model, or `realizeWith` bridge appears here — this checkpoint only
pins the countable substrate.
-/

namespace FirstOrder.Language

open Cardinal

variable {s₀ : LocalStage}

/-- Increasing `ℕ`-tuples of any fixed length are countable: the coercion to `Fin m → ℕ` is
injective, and `Fin m → ℕ` is countable. -/
instance instCountableFinOrderEmbNat (m : ℕ) : Countable (Fin m ↪o ℕ) :=
  (DFunLike.coe_injective (F := Fin m ↪o ℕ) (α := Fin m) (β := fun _ => ℕ)).countable

/-- **The schema sentence universe.** Over the base language `(localColim s₀)[[ℕ]]` (`ℕ` the
canonical indiscernible-sequence positions), the set of `templateSentence φ t` — "`φ` holds on
the constants `d_{t 0}, …, d_{t (m-1)}`" — as `⟨m, φ⟩` ranges over the colimit atom/connective
family `ΓEMlocal s₀` and `t` over the increasing `ℕ`-tuples of length `m`. This is the countable
decision list of the ω-stage completion; its `iSup`/`iInf` witnesses stay inside it because
`ΓEMlocal ⊇ ΓlocalColim` is component-closed. -/
def schemaSentenceUniverse (s₀ : LocalStage) : Set ((localColim s₀)[[ℕ]].Sentenceω) :=
  ⋃ (mφ ∈ ΓEMlocal s₀), Set.range fun t : Fin mφ.1 ↪o ℕ =>
    Lomega1omegaTemplate.templateSentence mφ.2 t

/-- **Checkpoint 1.** The schema sentence universe is countable — a countable union (over the
countable seed family `ΓEMlocal s₀`) of ranges of maps out of the countable tuple types. This is
what makes the ω-enumeration of the completion possible. -/
theorem schemaSentenceUniverse_countable : (schemaSentenceUniverse s₀).Countable :=
  (ΓEMlocal_countable s₀).biUnion fun _ _ => Set.countable_range _

/-- A canonical length-`m` increasing `ℕ`-tuple: the inclusion `Fin m ↪ ℕ` by value, which is
strictly monotone. Used to base-point the schema universe. -/
def stdTuple (m : ℕ) : Fin m ↪o ℕ :=
  OrderEmbedding.ofStrictMono (fun i => (i : ℕ)) fun _ _ h => h

/-- The schema sentence universe is nonempty: the seed family is nonempty
(`ΓEMlocal_nonempty`) and every arity admits the standard tuple, so the corresponding
`templateSentence` is a member. Supplies the base point the enumeration in checkpoint 3 needs. -/
theorem schemaSentenceUniverse_nonempty : (schemaSentenceUniverse s₀).Nonempty := by
  obtain ⟨mφ, hmφ⟩ := ΓEMlocal_nonempty s₀
  exact ⟨Lomega1omegaTemplate.templateSentence mφ.2 (stdTuple mφ.1),
    Set.mem_biUnion hmφ ⟨stdTuple mφ.1, rfl⟩⟩

/-! ## Checkpoint 2, step 1: the template-realization bridge

Connects MarkerStage's `realizeWith` (over the double Henkin expansion `((L''[[J]])[[ℕ]])`) to the
`templateSentence` semantics: the schema sentence `templateSentence ψ t`, lifted into the Marker
language along the Henkin inclusion, is `realizeWith`-true under a skeleton interpretation `σ`
exactly when `ψ` holds on the `σ`-images `i ↦ σ (t i)` of its constants. The Henkin layer is inert
(no Henkin constants occur). This is the semantic content the base certification (step 3) and the
seed agreement (7c) both consume. Stated generically in `L''`/`J`, so the two `constantsOn`
instances of `realizeWith` stay unambiguous (as at its definition site). -/

section TemplateBridge

variable {L'' : Language.{0, 0}} {J : Type} [LinearOrder J] {M : Type} [L''.Structure M]

/-- **The template-realization bridge.** `templateSentence ψ t` (over `L''[[J]]`), lifted into the
Marker double expansion `((L''[[J]])[[ℕ]])` along the Henkin inclusion, realizes under a skeleton
interpretation `σ : J → M` and any Henkin interpretation `h : ℕ → M` iff `ψ` holds on the tuple
`i ↦ σ (t i)`. Composes `sentenceRealize_iff_realizeWith`, `realize_mapLanguage` (the Henkin
inclusion is an expansion, `withConstants_expansion`), and the existing `realize_templateSentence`. -/
theorem realizeWith_templateSentence (σ : J → M) (h : ℕ → M)
    {n : ℕ} (ψ : L''.BoundedFormulaω Empty n) (t : Fin n ↪o J) :
    realizeWith σ h
        ((Lomega1omegaTemplate.templateSentence ψ t).mapLanguage
          ((L''[[J]]).lhomWithConstants ℕ))
        (Empty.elim : Empty → M) Fin.elim0
      ↔ ψ.Realize (Empty.elim : Empty → M) (fun i => σ (t i)) := by
  letI : (constantsOn J).Structure M := constantsOn.structure σ
  letI : (constantsOn ℕ).Structure M := constantsOn.structure h
  rw [← sentenceRealize_iff_realizeWith]
  show Sentenceω.Realize _ M ↔ _
  rw [Sentenceω.Realize]
  rw [BoundedFormulaω.realize_mapLanguage ((L''[[J]]).lhomWithConstants ℕ)
    (Lomega1omegaTemplate.templateSentence ψ t)]
  exact realize_templateSentence σ ψ t

end TemplateBridge

/-! ## Checkpoint 2: the empty base is Marker-consistent

The ω-stage completion (checkpoint 3) starts from the empty theory and decides every schema
sentence's sign via the already-proved `MarkerHenkinConsistent.extension` (which internally
homogenizes through `markerStage_homogeneous`). Since `schemaSentenceUniverse` is a *decision
list* — its canonical atoms include both true and false instances (e.g. `x₀ = x₁`) — the base is
NOT "all universe sentences are true"; it is the trivially-realizable empty fragment. The Morley
seed `{φ, x₀ ≠ x₁}` needs no explicit seeding: `extension` is forced to pick `φ` (its negation is
incompatible with `M ⊨ φ`) and distinctness (its negation is incompatible with the strictly
increasing skeleton interpretations). -/

section EmptyBase

variable {L'' : Language.{0, 0}} {J : Type} [LinearOrder J]
  {M : Type} [L''.Structure M] [LinearOrder M] [WellFoundedLT M]

/-- **Checkpoint 2.** The empty fragment is `MarkerHenkinConsistent M` for any source `M` of size
`≥ ℶ_ω₁`: at every level `β < ω₁` the body is the trivial certificate over the `(ℶ_β)⁺`-suborder
`e` supplied by `markerStage_homogeneous` at empty arity, with no members to realize. This is the
starting point the ω-stage `extension`/`iSup_choice` chain builds on. -/
theorem markerHenkinConsistent_empty
    (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M) :
    MarkerHenkinConsistent M (∅ : Finset (((L''[[J]])[[ℕ]]).Sentenceω)) := by
  haveI : Nonempty M := Cardinal.mk_ne_zero_iff.mp
    (((lt_of_lt_of_le Cardinal.aleph0_pos (Cardinal.aleph0_le_beth _)).trans_le hM).ne')
  refine ⟨∅, ∅, fun τ hτ => by simp at hτ, fun τ hτ => by simp at hτ, fun β hβ => ?_⟩
  obtain ⟨_, _, _, _, _, e, _⟩ :=
    markerStage_homogeneous (L' := L'') M hM β hβ (J := J)
      (m := 0) (ar := Fin.elim0) (fun p => p.elim0) (fun p => p.elim0)
  exact ⟨β, le_refl β, hβ, e, fun σ _ _ => ⟨fun _ => Classical.arbitrary M, fun τ hτ => by simp at hτ⟩⟩

end EmptyBase

end FirstOrder.Language
