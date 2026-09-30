/-
Regression guard for fragment elementarity of cocones and direct limits
(`ModelTheory/AElementaryDirectLimit.lean`), the cross-universe `AElementary`, and the shared
atomic-formula embedding lemmas (`Lomega1omega/Semantics.lean`).

Checked: the cocone theorem as conditional API composition, with no `DirectedSystem` instance, no
nonempty index and the target in its own universe; the direct-limit theorem with `A` and `f`
inferred from the transition hypothesis; the **higher-universe index with small carriers**
(`ι := ULift.{1} ℕ`, `G i : Type`, limit in `Type 1`), which the single-universe `AElementary`
could not state; the sentence wrapper and the theory wrapper applied; a **constant system** (every
component one structure, identity transitions), whose canonical maps are A-elementary with no
hypothesis; a **directed family of substructures** through the cocone theorem, with the
inclusions into the union as the cocone; `AElementary` across two carrier universes and its
`comp` across three; and the atomic-formula embedding lemmas.  Headline declarations use only the
standard axioms.

Run with: lake env lean scripts/check_aelementary_directlimit_regressions.lean
-/
import InfinitaryLogic.ModelTheory.AElementaryDirectLimit

open Lean FirstOrder Language

universe u v

/-- **Cocone form, conditional API composition**: no `DirectedSystem`, no `Nonempty ι`, and the
target `M : Type 2` in a universe unrelated to the components. -/
theorem cocone_regression {L : Language.{u, v}} {ι : Type} [Preorder ι] [IsDirectedOrder ι]
    {G : ι → Type} [∀ i, L.Structure (G i)] {f : ∀ i j, i ≤ j → G i ↪[L] G j} {M : Type 2}
    [L.Structure M] {g : ∀ i, G i ↪[L] M} {A : Fragment L}
    (hf : ∀ i j (h : i ≤ j), AElementary A (f i j h))
    (hg : ∀ i j (h : i ≤ j) x, g j (f i j h x) = g i x) (hcover : ∀ z : M, ∃ i x, g i x = z)
    (i : ι) : AElementary A (g i) :=
  aElementary_of_cocone hf hg hcover i

/-- **Direct limit, conditional API composition**: `A` and `f` are inferred from `hf`. -/
theorem directlimit_regression {L : Language.{u, v}} {ι : Type} [Preorder ι] [IsDirectedOrder ι]
    [Nonempty ι] {G : ι → Type} [∀ i, L.Structure (G i)] (f : ∀ i j, i ≤ j → G i ↪[L] G j)
    [DirectedSystem G fun i j h ↦ f i j h] (A : Fragment L)
    (hf : ∀ i j (h : i ≤ j), AElementary A (f i j h)) (i : ι) :
    AElementary A (DirectLimit.of L ι G f i) :=
  aElementary_directLimit_of hf i

/-- **Higher-universe index, small carriers**: the limit lives in `Type 1` while the components
live in `Type`; the theorem elaborates and applies. -/
theorem higher_universe_index_regression {L : Language.{0, 0}} {G : ULift.{1} ℕ → Type}
    [∀ i, L.Structure (G i)] (f : ∀ i j, i ≤ j → G i ↪[L] G j)
    [DirectedSystem G fun i j h ↦ f i j h] (A : Fragment L)
    (hf : ∀ i j (h : i ≤ j), AElementary A (f i j h)) (i : ULift.{1} ℕ) :
    AElementary A (DirectLimit.of L (ULift.{1} ℕ) G f i) ∧
    ((Language.DirectLimit G f : Type 1) = Language.DirectLimit G f) :=
  ⟨aElementary_directLimit_of hf i, rfl⟩

/-- **Sentence wrapper**: a fragment sentence transfers between the limit and a component. -/
theorem sentence_wrapper_regression {L : Language.{u, v}} {ι : Type} [Preorder ι]
    [IsDirectedOrder ι] [Nonempty ι] {G : ι → Type} [∀ i, L.Structure (G i)]
    (f : ∀ i j, i ≤ j → G i ↪[L] G j) [DirectedSystem G fun i j h ↦ f i j h] (A : Fragment L)
    (hf : ∀ i j (h : i ≤ j), AElementary A (f i j h)) (i : ι) (φ : L.Sentenceω)
    (hφ : (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A.toSet) :
    (Sentenceω.Realize φ (Language.DirectLimit G f) ↔ Sentenceω.Realize φ (G i)) :=
  realize_sentence_directLimit_iff hf i hφ

/-- **Theory wrapper**: a fragment theory is modelled by the limit iff by a component. -/
theorem theory_wrapper_regression {L : Language.{u, v}} {ι : Type} [Preorder ι]
    [IsDirectedOrder ι] [Nonempty ι] {G : ι → Type} [∀ i, L.Structure (G i)]
    (f : ∀ i j, i ≤ j → G i ↪[L] G j) [DirectedSystem G fun i j h ↦ f i j h] (A : Fragment L)
    (hf : ∀ i j (h : i ≤ j), AElementary A (f i j h)) (i : ι) (T : Set L.Sentenceω)
    (hT : ∀ φ ∈ T, (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A.toSet) :
    (Theoryω.Model T (Language.DirectLimit G f) ↔ Theoryω.Model T (G i)) :=
  theoryModel_directLimit_iff hf i hT

/-- The constant system on `N` with identity transitions is a directed system. -/
instance constDirectedSystem {L : Language.{u, v}} {ι : Type} [Preorder ι] {N : Type}
    [L.Structure N] :
    DirectedSystem (fun _ : ι ↦ N) fun _ _ _ ↦ (Embedding.refl L N : N → N) :=
  ⟨fun _ _ ↦ rfl, fun _ _ _ _ _ _ ↦ rfl⟩

/-- **Constant system**: every component is `N` and every transition is the identity, so the
transition hypothesis is `AElementary.refl` and each canonical map into the limit is
A-elementary outright. -/
theorem constant_system_regression {L : Language.{u, v}} {ι : Type} [Preorder ι]
    [IsDirectedOrder ι] [Nonempty ι] {N : Type} [L.Structure N] (A : Fragment L) (i : ι) :
    AElementary A (DirectLimit.of L ι (fun _ ↦ N) (fun _ _ _ ↦ Embedding.refl L N) i) :=
  aElementary_directLimit_of (fun _ _ _ ↦ AElementary.refl A) i

/-- **Directed family of substructures through the cocone form**: for a monotone family over a
nonempty directed index with pairwise A-elementary links, each link is A-elementary in the union;
the cocone is the inclusions into `⨆ i, S i`. -/
theorem substructure_cocone_regression {L : Language.{u, v}} {M : Type} [L.Structure M]
    {ι : Type} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] {S : ι → L.Substructure M}
    (hmono : Monotone S) (A : Fragment L)
    (hf : ∀ i j (h : i ≤ j), AElementary A (Substructure.inclusion (hmono h))) (i : ι) :
    AElementary A (Substructure.inclusion (le_iSup S i)) :=
  aElementary_of_cocone (g := fun i ↦ Substructure.inclusion (le_iSup S i)) hf
    (fun _ _ _ _ ↦ rfl)
    (fun z ↦ by
      obtain ⟨j, hj⟩ := (Substructure.mem_iSup_of_directed hmono.directed_le).mp z.2
      exact ⟨j, ⟨z, hj⟩, rfl⟩)
    i

/-- **Cross-universe `AElementary`**: two carrier universes in the predicate, three in `comp`. -/
theorem cross_universe_regression {L : Language.{u, v}} {M : Type 2} {N : Type 1} {P : Type}
    [L.Structure M] [L.Structure N] [L.Structure P] (A : Fragment L) (f : N ↪[L] M) (g : P ↪[L] N)
    (hf : AElementary A f) (hg : AElementary A g) : AElementary A (f.comp g) :=
  hf.comp hg

/-- **Atomic formulas along embeddings**: equality and relation atoms are preserved and reflected
at image valuations, across carrier universes. -/
theorem atomic_embedding_regression {L : Language.{u, v}} {M : Type} {N : Type 1}
    [L.Structure M] [L.Structure N] (f : M ↪[L] N) {α : Type} {n l : ℕ} (v : α → M)
    (xs : Fin n → M) (t₁ t₂ : L.Term (α ⊕ Fin n)) (R : L.Relations l)
    (ts : Fin l → L.Term (α ⊕ Fin n)) :
    ((BoundedFormulaω.equal t₁ t₂).Realize (⇑f ∘ v) (⇑f ∘ xs) ↔
      (BoundedFormulaω.equal t₁ t₂).Realize v xs) ∧
    ((BoundedFormulaω.rel R ts).Realize (⇑f ∘ v) (⇑f ∘ xs) ↔
      (BoundedFormulaω.rel R ts).Realize v xs) :=
  ⟨f.realize_equal_comp t₁ t₂, f.realize_rel_comp R ts⟩

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.aElementary_of_cocone,
   `FirstOrder.Language.aElementary_directLimit_of,
   `FirstOrder.Language.realize_sentence_directLimit_iff,
   `FirstOrder.Language.theoryModel_directLimit_iff,
   `FirstOrder.Language.Embedding.realize_equal_comp,
   `FirstOrder.Language.Embedding.realize_rel_comp,
   `FirstOrder.Language.AElementary.comp, `FirstOrder.Language.AElementary.of_comp,
   `FirstOrder.Language.aElementary_of_tarskiVaught,
   `cocone_regression, `directlimit_regression, `higher_universe_index_regression,
   `sentence_wrapper_regression, `theory_wrapper_regression, `constant_system_regression,
   `substructure_cocone_regression, `cross_universe_regression, `atomic_embedding_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "aelementary-directlimit regression guard: OK (cocone form without DirectedSystem or \
    Nonempty; direct limit with A and f inferred; higher-universe index with small carriers; \
    sentence and theory wrappers; constant system; directed substructure family via the cocone; \
    cross-universe AElementary and comp; atomic embedding lemmas; headline declarations on \
    standard axioms)"
