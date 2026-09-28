/-
Regression guard for Scott isolation and definability (`Descriptive/ScottDefinability.lean`).

A **concrete two-code example**: the language with one nullary predicate, the two codes on `ℕ` where
the predicate is false and where it is true, presented in `Bool` by the identity.  Isomorphic codes
are equal (an isomorphism preserves the nullary predicate), so the presentation is **isolated**
through the library theorem, with the isolating sentences applied to both values.  Then sentence
definability of the **empty**, a **singleton**, and the **two-element** set, and the
countable-or-cocountable **characterization** in both directions.  The abstract lemmas are
also exercised without relationality or signature countability in scope.  Headline declarations
use only the standard axioms.

Run with: lake env lean scripts/check_scott_definability_regressions.lean
-/
import InfinitaryLogic.Descriptive.ScottDefinability

open Lean FirstOrder Language

/-- The language with one nullary predicate and nothing else. -/
def nullLang : Language.{0, 0} where
  Functions _ := Empty
  Relations l := { _u : Unit // l = 0 }

instance : nullLang.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

instance : Countable (Σ l, nullLang.Relations l) :=
  inferInstanceAs (Countable (Σ l, { _u : Unit // l = 0 }))

/-- The nullary predicate. -/
def P₀ : nullLang.Relations 0 := ⟨(), rfl⟩

/-- The two codes: the predicate is `b` everywhere. -/
def codesOf (b : Bool) : StructureSpace nullLang := fun _ => b

/-- **Isomorphic codes are equal**: an isomorphism preserves the nullary predicate. -/
theorem codesOf_iso (b b' : Bool) (h : (structureIsoSetoid nullLang).r (codesOf b) (codesOf b')) :
    b = b' := by
  obtain ⟨e⟩ := h
  have := @Language.Equiv.map_rel' nullLang ℕ ℕ (codesOf b).toStructure (codesOf b').toStructure e
    0 P₀ Fin.elim0
  change codesOf b' _ = true ↔ codesOf b _ = true at this
  simp only [codesOf] at this
  cases b <;> cases b' <;> simp_all

/-- The presentation: `truth φ b` is satisfaction at the code for `b`. -/
def truthOf : nullLang.Sentenceω → Bool → Prop := fun φ b => codesOf b ∈ ModelsOf φ

/-- **Isolation** of the concrete presentation, with the isolating sentences applied to both
values. -/
theorem isolation_regression :
    IsolatedPresentation truthOf ∧
    (∃ σ : nullLang.Sentenceω, truthOf σ true ∧ ¬ truthOf σ false) ∧
    (∃ σ : nullLang.Sentenceω, truthOf σ false ∧ ¬ truthOf σ true) := by
  have hisol : IsolatedPresentation truthOf :=
    isolatedPresentation_of_surjective codesOf id Function.surjective_id
      (fun b b' h => codesOf_iso b b' h) truthOf (fun _ _ => Iff.rfl)
  refine ⟨hisol, ?_, ?_⟩
  · obtain ⟨σ, hσ⟩ := hisol true
    exact ⟨σ, (hσ true).mpr rfl, fun h => by have := (hσ false).mp h; simp at this⟩
  · obtain ⟨σ, hσ⟩ := hisol false
    exact ⟨σ, (hσ false).mpr rfl, fun h => by have := (hσ true).mp h; simp at this⟩

/-- **Definability** of the empty, a singleton, and the two-element set. -/
theorem definability_regression :
    (∃ φ : nullLang.Sentenceω, ∀ b, truthOf φ b ↔ b ∈ (∅ : Set Bool)) ∧
    (∃ φ : nullLang.Sentenceω, ∀ b, truthOf φ b ↔ b ∈ ({true} : Set Bool)) ∧
    (∃ φ : nullLang.Sentenceω, ∀ b, truthOf φ b ↔ b ∈ ({true, false} : Set Bool)) :=
  ⟨exists_sentence_of_countable_of_presentation codesOf id Function.surjective_id
      (fun b b' h => codesOf_iso b b' h) truthOf (fun _ _ => Iff.rfl) Set.countable_empty,
    exists_sentence_of_countable_of_presentation codesOf id Function.surjective_id
      (fun b b' h => codesOf_iso b b' h) truthOf (fun _ _ => Iff.rfl) (Set.countable_singleton _),
    exists_sentence_of_countable_of_presentation codesOf id Function.surjective_id
      (fun b b' h => codesOf_iso b b' h) truthOf (fun _ _ => Iff.rfl) (Set.to_countable _)⟩

/-- **The characterization**, both directions, on the concrete presentation. -/
theorem characterization_regression (S : Set Bool) :
    ((∃ φ : nullLang.Sentenceω, ∀ b, truthOf φ b ↔ b ∈ S) → S.Countable ∨ Sᶜ.Countable) ∧
    (S.Countable ∨ Sᶜ.Countable → ∃ φ : nullLang.Sentenceω, ∀ b, truthOf φ b ↔ b ∈ S) :=
  let h := sentence_definable_iff_of_presentation codesOf id Function.surjective_id
    (fun b b' h => codesOf_iso b b' h) truthOf (fun _ _ => Iff.rfl)
    (fun _ => Or.inl (Set.to_countable _)) S
  ⟨h.mp, h.mpr⟩

/-- **The abstract layer needs no relationality or signature countability**: an arbitrary language
and an arbitrary presentation type, with the closure data as hypotheses. -/
theorem abstract_regression {L : Language.{0, 0}} {Q : Type} (truth : L.Sentenceω → Q → Prop)
    (hisol : IsolatedPresentation truth)
    (hesup : ∀ (φs : ℕ → L.Sentenceω) q,
      truth (BoundedFormulaω.esup φs) q ↔ ∃ n, truth (φs n) q)
    (hbot : ∀ q, ¬ truth BoundedFormulaω.falsum q) (S : Set Q) (hS : S.Countable) :
    ∃ φ : L.Sentenceω, ∀ q, truth φ q ↔ q ∈ S :=
  exists_sentence_of_countable hisol hesup hbot hS

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.exists_sentence_of_countable, `FirstOrder.Language.sentence_definable_iff,
   `FirstOrder.Language.isolatedPresentation_of_surjective,
   `FirstOrder.Language.exists_sentence_of_countable_of_presentation,
   `FirstOrder.Language.sentence_definable_iff_of_presentation,
   `codesOf_iso, `isolation_regression, `definability_regression, `characterization_regression,
   `abstract_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "scott-definability regression guard: OK (concrete two-code nullary example: isolation \
    applied to both values, definability of the empty, singleton, and two-element sets, the \
    characterization both ways; abstract layer without relationality or countability; headline \
    declarations on standard axioms)"
