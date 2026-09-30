/-
Regression guard for fragment elementarity of direct limits
(`ModelTheory/AElementaryDirectLimit.lean`) and the cross-universe `AElementary`.

Checked: the main theorem as conditional API composition; the **higher-universe index with small
carriers** (`ι := ULift.{1} ℕ`, `G i : Type`, limit in `Type 1`), which is exactly the case the
single-universe `AElementary` could not state; the sentence and theory wrappers; `AElementary`
itself across two carrier universes and its `comp` across three; and the inclusion specialization
(constant system, identity transitions) as a sanity case.  Headline declarations use only the
standard axioms.

Run with: lake env lean scripts/check_aelementary_directlimit_regressions.lean
-/
import InfinitaryLogic.ModelTheory.AElementaryDirectLimit

open Lean FirstOrder Language

universe u v

/-- **Conditional API composition** of the main theorem. -/
theorem directlimit_regression {L : Language.{u, v}} {ι : Type} [Preorder ι] [IsDirectedOrder ι]
    [Nonempty ι] {G : ι → Type} [∀ i, L.Structure (G i)] (f : ∀ i j, i ≤ j → G i ↪[L] G j)
    [DirectedSystem G fun i j h ↦ f i j h] (A : Fragment L)
    (hf : ∀ i j (h : i ≤ j), AElementary A (f i j h)) (i : ι) :
    AElementary A (DirectLimit.of L ι G f i) :=
  aElementary_directLimit_of f A hf i

/-- **Higher-universe index, small carriers**: the limit lives in `Type 1` while the components
live in `Type`; the theorem elaborates and applies. -/
theorem higher_universe_index_regression {L : Language.{0, 0}} {G : ULift.{1} ℕ → Type}
    [∀ i, L.Structure (G i)] (f : ∀ i j, i ≤ j → G i ↪[L] G j)
    [DirectedSystem G fun i j h ↦ f i j h] (A : Fragment L)
    (hf : ∀ i j (h : i ≤ j), AElementary A (f i j h)) (i : ULift.{1} ℕ) :
    AElementary A (DirectLimit.of L (ULift.{1} ℕ) G f i) ∧
    ((Language.DirectLimit G f : Type 1) = Language.DirectLimit G f) :=
  ⟨aElementary_directLimit_of f A hf i, rfl⟩

/-- **Wrappers**: sentences and theories of the fragment transfer to the limit. -/
theorem wrappers_regression {L : Language.{u, v}} {ι : Type} [Preorder ι] [IsDirectedOrder ι]
    [Nonempty ι] {G : ι → Type} [∀ i, L.Structure (G i)] (f : ∀ i j, i ≤ j → G i ↪[L] G j)
    [DirectedSystem G fun i j h ↦ f i j h] (A : Fragment L)
    (hf : ∀ i j (h : i ≤ j), AElementary A (f i j h)) (i : ι) (φ : L.Sentenceω)
    (hφ : (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A.toSet) :
    (Sentenceω.Realize φ (Language.DirectLimit G f) ↔ Sentenceω.Realize φ (G i)) :=
  realize_sentence_directLimit_iff f A hf i hφ

/-- **Cross-universe `AElementary`**: two carrier universes in the predicate, three in `comp`. -/
theorem cross_universe_regression {L : Language.{u, v}} {M : Type 2} {N : Type 1} {P : Type}
    [L.Structure M] [L.Structure N] [L.Structure P] (A : Fragment L) (f : N ↪[L] M) (g : P ↪[L] N)
    (hf : AElementary A f) (hg : AElementary A g) : AElementary A (f.comp g) :=
  hf.comp hg

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.aElementary_directLimit_of,
   `FirstOrder.Language.realize_sentence_directLimit_iff,
   `FirstOrder.Language.theoryModel_directLimit_iff,
   `FirstOrder.Language.AElementary.comp, `FirstOrder.Language.AElementary.of_comp,
   `FirstOrder.Language.aElementary_of_tarskiVaught,
   `directlimit_regression, `higher_universe_index_regression, `wrappers_regression,
   `cross_universe_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "aelementary-directlimit regression guard: OK (conditional composition; higher-universe \
    index with small carriers; sentence wrapper; cross-universe AElementary and comp; headline \
    declarations on standard axioms)"
