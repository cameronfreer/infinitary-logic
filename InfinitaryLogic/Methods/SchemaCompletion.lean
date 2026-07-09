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

/-! ## Checkpoint 3a: the lifted universe and its `FSentence` membership

The ω-stage completion runs over `((localColim s₀)[[ℕ]])[[ℕ]]` (`FSentence`), so the universe must
be lifted along the same Henkin inclusion as the bridge. Two `functionsIn`-under-`mapLanguage`
facts (absent from the existing `relabel`/`subst`/`openBounds` API) drive the constant-support
computation: lifting sends every function symbol to its `Sum.inl` image, so it produces **no**
Henkin constants and preserves the skeleton-constant support. A lifted `templateSentence ψ t` then
has finite constant support `image t` (and empty Henkin support) — regardless of how many base
function symbols the (possibly `iSup`-branching) `ψ` uses, because `HasFiniteConstSupport` bounds
only the *constant* symbols, never all of `functionsIn`. -/

section FunctionsInMapLanguage

variable {L L' : Language.{0, 0}} (g : L →ᴸ L')

/-- `functionsIn` of a language-mapped term is the image of the term's `functionsIn` under the
symbol map `⟨n, f⟩ ↦ ⟨n, g.onFunction f⟩`. -/
theorem Term.functionsIn_onTerm {α : Type} (t : L.Term α) :
    (g.onTerm t).functionsIn =
      (fun p : Σ n, L.Functions n => ⟨p.1, g.onFunction p.2⟩) '' t.functionsIn := by
  induction t with
  | var x => simp [LHom.onTerm, Term.functionsIn]
  | func f ts ih =>
    simp only [LHom.onTerm, Term.functionsIn, Set.image_insert_eq, Set.image_iUnion, ih]

/-- `functionsIn` of a language-mapped formula is the image of the formula's `functionsIn` under
the symbol map `⟨n, f⟩ ↦ ⟨n, g.onFunction f⟩`. -/
theorem BoundedFormulaω.functionsIn_mapLanguage {α : Type} {n : ℕ}
    (φ : L.BoundedFormulaω α n) :
    (φ.mapLanguage g).functionsIn =
      (fun p : Σ n, L.Functions n => ⟨p.1, g.onFunction p.2⟩) '' φ.functionsIn := by
  induction φ with
  | falsum => simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.functionsIn]
  | equal t u =>
    simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.functionsIn, Term.functionsIn_onTerm,
      Set.image_union]
  | rel R ts =>
    simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.functionsIn, Term.functionsIn_onTerm,
      Set.image_iUnion]
  | imp φ ψ ihφ ihψ =>
    simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.functionsIn, ihφ, ihψ, Set.image_union]
  | all φ ih => simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.functionsIn, ih]
  | iSup φs ih =>
    simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.functionsIn, ih, Set.image_iUnion]
  | iInf φs ih =>
    simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.functionsIn, ih, Set.image_iUnion]

end FunctionsInMapLanguage

section HenkinLiftSupport

variable {L'' : Language.{0, 0}} {J : Type}

/-- The Henkin inclusion `(L''[[J]]) →ᴸ ((L''[[J]])[[ℕ]])` sends every function symbol to its
`Sum.inl` image; hence a lifted formula has **no** Henkin constants. -/
theorem henkinConstsIn_mapLanguage {α : Type} {n : ℕ} (τ : (L''[[J]]).BoundedFormulaω α n) :
    henkinConstsIn (L'' := L'') (τ.mapLanguage ((L''[[J]]).lhomWithConstants ℕ)) = ∅ := by
  ext m
  simp only [henkinConstsIn, sentenceJConsts, Set.mem_setOf_eq,
    BoundedFormulaω.functionsIn_mapLanguage, Set.mem_image, Set.mem_empty_iff_false, iff_false,
    not_exists, not_and]
  rintro ⟨k, f⟩ _ heq
  rw [Sigma.mk.injEq] at heq
  obtain ⟨rfl, heq2⟩ := heq
  rw [heq_eq_eq] at heq2
  simp at heq2

/-- The Henkin inclusion preserves the skeleton (`J`) constant support: the expansion `J`-constants
of a lifted formula are exactly the `J`-constants of the original. -/
theorem expJConstsIn_mapLanguage {α : Type} {n : ℕ} (τ : (L''[[J]]).BoundedFormulaω α n) :
    expJConstsIn (L'' := L'') (τ.mapLanguage ((L''[[J]]).lhomWithConstants ℕ)) =
      sentenceJConsts (L' := L'') (J := J) τ := by
  ext j
  simp only [expJConstsIn, sentenceJConsts, Set.mem_setOf_eq,
    BoundedFormulaω.functionsIn_mapLanguage, Set.mem_image]
  constructor
  · rintro ⟨⟨k, f⟩, hf, heq⟩
    rw [Sigma.mk.injEq] at heq
    obtain ⟨rfl, heq2⟩ := heq
    rw [heq_eq_eq] at heq2
    have hf2 : f = Sum.inr j := Sum.inl_injective heq2
    exact hf2 ▸ hf
  · intro hj
    exact ⟨⟨0, Sum.inr j⟩, hj, rfl⟩

end HenkinLiftSupport

section TemplateSupport

variable {L'' : Language.{0, 0}} {J : Type} [LinearOrder J]

/-- The only `J`-constants of a `templateSentence ψ t` are the tuple's constants: substitution
introduces exactly `{t 0, …, t (n-1)}` and the `mapLanguage`d body contributes only base
(`Sum.inl`) symbols. -/
theorem sentenceJConsts_templateSentence {n : ℕ} (ψ : L''.BoundedFormulaω Empty n)
    (t : Fin n ↪o J) :
    sentenceJConsts (L' := L'') (J := J) (Lomega1omegaTemplate.templateSentence ψ t)
      ⊆ Set.range (⇑t) := by
  intro j hj
  simp only [sentenceJConsts, Set.mem_setOf_eq, Lomega1omegaTemplate.templateSentence] at hj
  have hsub := BoundedFormulaω.functionsIn_subst
    (fun i => Term.func (Sum.inr (t i) : (L''[[J]]).Functions 0) Fin.elim0)
    ((ψ.mapLanguage (L''.lhomWithConstants J)).openBounds) hj
  rw [BoundedFormulaω.functionsIn_openBounds] at hsub
  rcases hsub with hbody | hconst
  · rw [BoundedFormulaω.functionsIn_mapLanguage] at hbody
    obtain ⟨⟨k, f⟩, -, heq⟩ := hbody
    rw [Sigma.mk.injEq] at heq
    obtain ⟨rfl, heq2⟩ := heq
    rw [heq_eq_eq] at heq2
    exact absurd heq2 (by simp)
  · simp only [Set.mem_iUnion, Term.functionsIn, Set.iUnion_of_empty,
      Set.mem_insert_iff, Set.mem_empty_iff_false, or_false] at hconst
    obtain ⟨i, hi⟩ := hconst
    rw [Sigma.mk.injEq] at hi
    obtain ⟨-, hi2⟩ := hi
    rw [heq_eq_eq] at hi2
    exact ⟨i, (Sum.inr_injective hi2).symm⟩

/-- **Every lifted `templateSentence` is an `FSentence`.** Its expansion `J`-support is the finite
tuple image `image t`, and its Henkin support is empty. -/
theorem hasFiniteConstSupport_mapLanguage_templateSentence {n : ℕ}
    (ψ : L''.BoundedFormulaω Empty n) (t : Fin n ↪o J) :
    HasFiniteConstSupport (L'' := L'')
      ((Lomega1omegaTemplate.templateSentence ψ t).mapLanguage
        ((L''[[J]]).lhomWithConstants ℕ)) := by
  refine ⟨Finset.image (⇑t) Finset.univ, ∅, ?_, ?_⟩
  · rw [expJConstsIn_mapLanguage]
    intro j hj
    obtain ⟨i, hi⟩ := sentenceJConsts_templateSentence ψ t hj
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
  · rw [henkinConstsIn_mapLanguage]; exact Set.empty_subset _

end TemplateSupport

section LiftedUniverse

variable {s₀ : LocalStage}

/-- **The lifted schema universe**, as a set of `FSentence`s over the Marker language
`((localColim s₀)[[ℕ]])[[ℕ]]`: each schema sentence `templateSentence ψ t` (`⟨m, ψ⟩ ∈ ΓEMlocal`),
lifted along the Henkin inclusion and packaged with its finite-support proof. This is the
enumeration domain the ω-stage completion (checkpoint 3b) decides. -/
def schemaFSentenceUniverse (s₀ : LocalStage) :
    Set (FSentence (L'' := localColim s₀) (J := ℕ)) :=
  ⋃ (mφ ∈ ΓEMlocal s₀), Set.range fun t : Fin mφ.1 ↪o ℕ =>
    (⟨(Lomega1omegaTemplate.templateSentence mφ.2 t).mapLanguage
        (((localColim s₀)[[ℕ]]).lhomWithConstants ℕ),
      hasFiniteConstSupport_mapLanguage_templateSentence mφ.2 t⟩ :
      FSentence (L'' := localColim s₀) (J := ℕ))

/-- **Checkpoint 3a.** The lifted schema `FSentence` universe is countable — the enumeration the
completion needs exists. -/
theorem schemaFSentenceUniverse_countable : (schemaFSentenceUniverse s₀).Countable :=
  (ΓEMlocal_countable s₀).biUnion fun _ _ => Set.countable_range _

/-- The lifted schema `FSentence` universe is nonempty (base point for the enumeration). -/
theorem schemaFSentenceUniverse_nonempty : (schemaFSentenceUniverse s₀).Nonempty := by
  obtain ⟨mφ, hmφ⟩ := ΓEMlocal_nonempty s₀
  exact ⟨_, Set.mem_biUnion hmφ ⟨stdTuple mφ.1, rfl⟩⟩

end LiftedUniverse

/-! ## Checkpoint 3b: the ω-stage completion (subtype recursion)

A constructive Henkin enumeration over `ρ : ℕ → FSentence`. Each `stageStep` decides `ρ n` via
`extension` (branching on decidable consistency of the positive insert — `extension`'s `∨` is a
`Prop` and cannot eliminate into the `Subtype`), and, opportunistically and locally, if the
positive branch is `iSup`-shaped adjoins a witness via `iSup_choice`. The step carries a clean
disjunction `(positive ∧ iSup-witnessed) ∨ negative`, so the per-stage facts 3c consumes are
projections — no global classifier, no "φ ∉ F" discharge. -/

section Completion

variable {s₀ : LocalStage} {M : Type} [(localColim s₀).Structure M] [LinearOrder M]
  [WellFoundedLT M] (ρ : ℕ → FSentence (L'' := localColim s₀) (J := ℕ))

/-- **The stage step.** Given a consistent finite stage `Fp`, decide `ρ n` and (locally) witness a
positive `iSup`. Returns the next stage with consistency, monotonicity, and the decision record
`(positive ∧ iSup-witnessed) ∨ negative`. -/
noncomputable def stageStep
    (Fp : {F : Finset (((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω) // MarkerHenkinConsistent M F})
    (n : ℕ) :
    {G : Finset (((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω) //
      MarkerHenkinConsistent M G ∧ Fp.1 ⊆ G ∧
      (((ρ n).1 ∈ G ∧ ∀ φs, (ρ n).1 = BoundedFormulaω.iSup φs → ∃ k, φs k ∈ G) ∨
        (ρ n).1.not ∈ G)} := by
  classical
  by_cases hpos : MarkerHenkinConsistent M (insert (ρ n).1 Fp.1)
  · by_cases hSup : ∃ φs, (ρ n).1 = BoundedFormulaω.iSup φs
    · have hφs : (ρ n).1 = BoundedFormulaω.iSup (Classical.choose hSup) :=
        Classical.choose_spec hSup
      have hmem : BoundedFormulaω.iSup (Classical.choose hSup) ∈ insert (ρ n).1 Fp.1 :=
        hφs ▸ Finset.mem_insert_self _ _
      have hk := Classical.choose_spec (MarkerHenkinConsistent.iSup_choice hpos hmem)
      set k := Classical.choose (MarkerHenkinConsistent.iSup_choice hpos hmem)
      refine ⟨insert (Classical.choose hSup k) (insert (ρ n).1 Fp.1), hk,
        (Finset.subset_insert _ _).trans (Finset.subset_insert _ _),
        Or.inl ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), fun φs' hφs' => ?_⟩⟩
      have hφeq : Classical.choose hSup = φs' := by
        have h := hφs.symm.trans hφs'
        rwa [BoundedFormulaω.iSup.injEq] at h
      exact ⟨k, by rw [← congrFun hφeq k]; exact Finset.mem_insert_self _ _⟩
    · refine ⟨insert (ρ n).1 Fp.1, hpos, Finset.subset_insert _ _,
        Or.inl ⟨Finset.mem_insert_self _ _, fun φs' hφs' => ?_⟩⟩
      exact absurd ⟨φs', hφs'⟩ hSup
  · have hneg := (MarkerHenkinConsistent.extension Fp.2 (ρ n).1 (ρ n).2).resolve_left hpos
    exact ⟨insert (ρ n).1.not Fp.1, hneg, Finset.subset_insert _ _,
      Or.inr (Finset.mem_insert_self _ _)⟩

/-- **The completion stages.** `T 0 = ∅`; `T (n+1)` is the `stageStep` of `T n`. -/
noncomputable def schemaCompletionStage
    (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M) :
    ℕ → {F : Finset (((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω) // MarkerHenkinConsistent M F}
  | 0 => ⟨∅, markerHenkinConsistent_empty hM⟩
  | n + 1 =>
    ⟨(stageStep ρ (schemaCompletionStage hM n) n).1,
      (stageStep ρ (schemaCompletionStage hM n) n).2.1⟩

omit [WellFoundedLT M] in
/-- **`C0` at the consistency level**: a `MarkerHenkinConsistent` fragment contains no sentence
together with its negation (a body at some level realizes both, contradicting `realizeWith_not`). -/
theorem markerHenkinConsistent_not_mem_and_not_mem
    {F : Finset (((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω)} (h : MarkerHenkinConsistent M F)
    (τ : ((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω) : ¬(τ ∈ F ∧ τ.not ∈ F) := by
  rintro ⟨h1, h2⟩
  obtain ⟨S, H, hS, hH, hcof⟩ := h
  obtain ⟨α, -, -, e, hsat⟩ := hcof 0 (Ordinal.omega_pos 1)
  obtain ⟨σ, hmono, hrange⟩ := exists_strictMonoOn_interp e S
  obtain ⟨hval, hh⟩ := hsat σ hmono hrange
  exact (realizeWith_not σ hval τ _ _).mp
    (hh τ.not (Finset.mem_coe.mpr h2)) (hh τ (Finset.mem_coe.mpr h1))

variable (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M)

/-- Each stage is `MarkerHenkinConsistent` (built into the subtype). -/
theorem schemaCompletionStage_consistent (n : ℕ) :
    MarkerHenkinConsistent M (schemaCompletionStage ρ hM n).1 :=
  (schemaCompletionStage ρ hM n).2

/-- One-step monotonicity: a stage is contained in its successor. -/
theorem schemaCompletionStage_subset_succ (n : ℕ) :
    (schemaCompletionStage ρ hM n).1 ⊆ (schemaCompletionStage ρ hM (n + 1)).1 :=
  (stageStep ρ (schemaCompletionStage ρ hM n) n).2.2.1

/-- Monotonicity of the completion chain. -/
theorem schemaCompletionStage_mono {m n : ℕ} (h : m ≤ n) :
    (schemaCompletionStage ρ hM m).1 ⊆ (schemaCompletionStage ρ hM n).1 := by
  induction n with
  | zero => rw [Nat.le_zero.mp h]
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | rfl
    · exact (ih (Nat.lt_succ_iff.mp h')).trans (schemaCompletionStage_subset_succ ρ hM n)
    · exact subset_rfl

/-- **Stage `n` decides `ρ n`**: after stage `n+1`, either `(ρ n).1` or its negation is present. -/
theorem schemaCompletionStage_decides (n : ℕ) :
    (ρ n).1 ∈ (schemaCompletionStage ρ hM (n + 1)).1 ∨
      (ρ n).1.not ∈ (schemaCompletionStage ρ hM (n + 1)).1 := by
  rcases (stageStep ρ (schemaCompletionStage ρ hM n) n).2.2.2 with ⟨hmem, -⟩ | hneg
  · exact Or.inl hmem
  · exact Or.inr hneg

/-- **Stage `n` witnesses a positive `iSup`**: if `(ρ n).1` is `iSup φs` and lands positively in
stage `n+1`, some component `φs k` is present too. -/
theorem schemaCompletionStage_witness (n : ℕ) {φs : ℕ → ((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω}
    (hiSup : (ρ n).1 = BoundedFormulaω.iSup φs)
    (hpos : (ρ n).1 ∈ (schemaCompletionStage ρ hM (n + 1)).1) :
    ∃ k, φs k ∈ (schemaCompletionStage ρ hM (n + 1)).1 := by
  rcases (stageStep ρ (schemaCompletionStage ρ hM n) n).2.2.2 with ⟨-, hwit⟩ | hneg
  · exact hwit φs hiSup
  · exact absurd ⟨hpos, hneg⟩
      (markerHenkinConsistent_not_mem_and_not_mem
        (schemaCompletionStage_consistent ρ hM (n + 1)) (ρ n).1)

end Completion

end FirstOrder.Language
