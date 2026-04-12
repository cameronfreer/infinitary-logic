/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Theory
import InfinitaryLogic.Methods.Henkin.ModelExistence
import InfinitaryLogic.Methods.Henkin.SatisfiableConsistencyProperty
import InfinitaryLogic.Lomega1omega.Operations
import Mathlib.ModelTheory.LanguageMap
import Architect

/-!
# Downward Löwenheim-Skolem for Lω₁ω

This file proves the downward Löwenheim-Skolem theorem for Lω₁ω:
any Lω₁ω sentence satisfied by a countable model in a countable language
has a countable model (in any target universe).

## Main Results

- `downward_LS_with_naming`: Any satisfiable Lω₁ω sentence has a countable model,
  given a naming function (no countability assumption on the original model).
- `downward_LS`: Any Lω₁ω sentence satisfied by a countable model (`[Countable M]`)
  has a countable model. Uses language extension `L[[M]]`, requiring M countable.

## Implementation Notes

The proof constructs a `ConsistencyPropertyEq` from the given model M using
the "true in M" consistency property. To provide witnesses for the C7 quantifier
axioms, we extend the language L with constants naming each element of M,
then apply the model existence theorem in the extended language, and restrict
the resulting countable model back to L.

For languages where every element of M is already named by a closed term
(e.g., after Skolemization or in Henkin languages), we can work directly
in L without extension using `NamingFunction`.

## References

- [Mar16]
- [KK04]
-/

universe u u' v v' w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure

/-- The naming function for the extended language `L[[M]]`: each element `m : M`
is named by the constant symbol `L.con m`, which evaluates to `m` in the
canonical `L[[M]]`-structure on `M`. -/
@[blueprint "def:naming-function-with-constants"
  (title := /-- Naming function with constants -/)
  (statement := /-- The naming function for the extended language $L[[M]]$: each
    element $m \in M$ is named by the constant symbol $\operatorname{con}(m)$. -/)]
noncomputable def namingFunctionWithConstants (L : Language.{u, v}) (M : Type u) [L.Structure M] :
    NamingFunction L[[M]] M where
  name m := Term.func (Sum.inr m : L[[M]].Functions 0) Fin.elim0
  sound m := by
    simp only [Term.realize]
    rfl

/-- The sum language `L.sum L'` has countable function symbols when both L and L' do. -/
instance countable_sum_functions
    (L₁ : Language.{u, v}) (L₂ : Language.{u', v'})
    [Countable (Σ l, L₁.Functions l)] [Countable (Σ l, L₂.Functions l)] :
    Countable (Σ l, (L₁.sum L₂).Functions l) :=
  Countable.of_equiv _ (Equiv.sigmaSumDistrib L₁.Functions L₂.Functions).symm

/-- The sum language `L.sum L'` has countable relation symbols when both L and L' do. -/
instance countable_sum_relations
    (L₁ : Language.{u, v}) (L₂ : Language.{u', v'})
    [Countable (Σ l, L₁.Relations l)] [Countable (Σ l, L₂.Relations l)] :
    Countable (Σ l, (L₁.sum L₂).Relations l) :=
  Countable.of_equiv _ (Equiv.sigmaSumDistrib L₁.Relations L₂.Relations).symm

/-- The constantsOn language has countable function symbols when the index type is countable. -/
instance countable_constantsOn_functions (α : Type*) [Countable α] :
    Countable (Σ l, (constantsOn α).Functions l) := by
  change Countable (Σ l, constantsOnFunc α l)
  let e : α ≃ Σ l, constantsOnFunc α l :=
    { toFun := fun a => ⟨0, a⟩
      invFun := fun ⟨l, f⟩ => match l, f with | 0, c => c | _ + 1, c => c.elim
      left_inv := fun _ => rfl
      right_inv := fun ⟨l, f⟩ => match l, f with | 0, _ => rfl | _ + 1, c => c.elim }
  exact Countable.of_equiv α e

/-- The constantsOn language has countable relation symbols (they're all empty). -/
instance countable_constantsOn_relations (α : Type*) :
    Countable (Σ l, (constantsOn α).Relations l) :=
  have : IsEmpty (Σ l, (constantsOn α).Relations l) :=
    ⟨fun ⟨_, e⟩ => (e : Empty).elim⟩
  inferInstance

/-- L[[M]] has countable function symbols when L does and M is countable. -/
private instance withConstants_countable_functions (M : Type u) [Countable M]
    [Countable (Σ l, L.Functions l)] :
    Countable (Σ l, L[[M]].Functions l) :=
  countable_sum_functions L (constantsOn M)

/-- L[[M]] has countable relation symbols when L does. -/
private instance withConstants_countable_relations (M : Type u)
    [Countable (Σ l, L.Relations l)] :
    Countable (Σ l, L[[M]].Relations l) :=
  countable_sum_relations L (constantsOn M)

/-- **Downward Löwenheim-Skolem with naming function**: If a countable language has
a naming function (every element is named by a closed term), then any satisfiable
sentence has a countable model.

This is the version that avoids language extension by assuming a naming function
already exists. In practice, this applies to Henkin languages and term models. -/
theorem downward_LS_with_naming
    [Countable (Σ l, L.Functions l)] [Countable (Σ l, L.Relations l)]
    (φ : L.Sentenceω) (M : Type*) [L.Structure M]
    (ι : NamingFunction L M)
    (hM : Sentenceω.Realize φ M) :
    ∃ (N : Type u) (_ : L.Structure N) (_ : Countable N),
      Sentenceω.Realize φ N := by
  obtain ⟨N, hStr, hCount, hModel⟩ :=
    model_existence (trueInModelConsistencyPropertyEq M ι) {φ}
      (singleton_in_trueInModelSets ι φ hM) (Set.countable_singleton φ)
  exact ⟨N, hStr, hCount, hModel φ (Set.mem_singleton φ)⟩

/-- **Downward Löwenheim-Skolem for theories with naming function**.
A corollary of `consistent_theory_has_model`. -/
theorem downward_LS_theory_with_naming
    [Countable (Σ l, L.Functions l)] [Countable (Σ l, L.Relations l)]
    (T : L.Theoryω) (M : Type*) [L.Structure M]
    (ι : NamingFunction L M)
    (hM : T.Model M) (hT_countable : T.Countable) :
    ∃ (N : Type u) (_ : L.Structure N) (_ : Countable N),
      T.Model N :=
  consistent_theory_has_model (trueInModelConsistencyPropertyEq M ι) T
    (subset_trueInModel_in_sets ι T hM) hT_countable

/-- **Downward Löwenheim-Skolem for Lω₁ω**: Any satisfiable sentence in a countable
language with a countable model has a countable model (in universe `u`).

The proof extends L with constants for each element of M to form `L[[M]]`, constructs
a naming function, applies model existence, then restricts back. The countability
condition on M is needed so that `L[[M]]` remains countable.

For the version without the `[Countable M]` assumption (but with a naming function
already available), see `downward_LS_with_naming`. -/
@[blueprint "thm:downward-ls"
  (title := /-- Downward Löwenheim-Skolem -/)
  (statement := /-- Given a countable model $M$ of an $\Lomegaone$ sentence $\varphi$
    in a countable language, one can construct a countable model in the same
    universe as $M$ via language expansion $L[[M]]$ and the model existence theorem. -/)
  (proof := /-- The key step is the language expansion: extend $L$ with a constant
    for each element of $M$ to form $L[[M]]$, which remains countable. A naming
    function witnessing the constants lets us build a consistency property in
    $L[[M]]$; the model existence theorem then produces a fresh countable term
    model $N$, which we restrict back to $L$. -/)
  (proofUses := ["def:naming-function-with-constants", "thm:model-existence"])]
theorem downward_LS [Countable (Σ l, L.Functions l)] [Countable (Σ l, L.Relations l)]
    (φ : L.Sentenceω) (M : Type u) [L.Structure M] [Countable M]
    (hM : Sentenceω.Realize φ M) :
    ∃ (N : Type u) (_ : L.Structure N) (_ : Countable N),
      Sentenceω.Realize φ N := by
  -- Step 1: Extend L with constants for M. L[[M]] is countable since L and M are.
  letI := Language.withConstantsSelfStructure (L := L) (M := M)
  -- Step 2: Lift φ to L[[M]]
  let φ' : L[[M]].Sentenceω := φ.mapLanguage (L.lhomWithConstants M)
  -- Step 3: φ' is true in M (by realize_mapLanguage with the expansion)
  have hM' : Sentenceω.Realize φ' M := by
    simp only [φ', Sentenceω.Realize]
    rw [BoundedFormulaω.realize_mapLanguage]
    exact hM
  -- Step 4: Apply downward_LS_with_naming in L[[M]]
  obtain ⟨N, hStrN, hCountN, hNφ'⟩ :=
    downward_LS_with_naming φ' M (namingFunctionWithConstants L M) hM'
  -- Step 5: Restrict N from L[[M]] back to L
  letI : L.Structure N := (L.lhomWithConstants M).reduct N
  exact ⟨N, inferInstance, hCountN, by
    simp only [Sentenceω.Realize]
    have := hNφ'
    simp only [φ', Sentenceω.Realize] at this
    rwa [BoundedFormulaω.realize_mapLanguage] at this⟩

/-- Downward LS for theories: any Lω₁ω theory in a countable language
satisfied by a countable model (`[Countable M]`) has a countable model. -/
@[blueprint "thm:downward-ls-theory"
  (title := /-- Downward Löwenheim-Skolem for theories -/)
  (statement := /-- Given a countable model $M$ of a countable $\Lomegaone$ theory $T$
    in a countable language, one can reconstruct a countable model in the same
    universe as $M$ via language expansion $L[[M]]$ and the model existence theorem. -/)
  (proof := /-- Same language-expansion strategy as the sentence version: lift the
    entire theory to $L[[M]]$, use the naming function to build a consistency
    property witnessing all sentences, apply model existence for the countable
    term model, then restrict the $L[[M]]$-structure back to $L$. -/)
  (proofUses := ["def:naming-function-with-constants", "thm:model-existence"])]
theorem downward_LS_theory [Countable (Σ l, L.Functions l)] [Countable (Σ l, L.Relations l)]
    (T : L.Theoryω) (M : Type u) [L.Structure M] [Countable M]
    (hM : T.Model M) (hT_countable : T.Countable) :
    ∃ (N : Type u) (_ : L.Structure N) (_ : Countable N),
      T.Model N := by
  -- Lift T to L[[M]], apply model_existence, restrict back
  letI := Language.withConstantsSelfStructure (L := L) (M := M)
  let ι := namingFunctionWithConstants L M
  -- The lifted theory
  let T' : Set L[[M]].Sentenceω := BoundedFormulaω.mapLanguage (L.lhomWithConstants M) '' T
  have hT'_countable : T'.Countable := hT_countable.image _
  -- All sentences in T' are true in M
  have hM' : ∀ σ' ∈ T', Sentenceω.Realize σ' M := by
    rintro _ ⟨σ, hσ, rfl⟩
    simp only [Sentenceω.Realize]
    rw [BoundedFormulaω.realize_mapLanguage]
    exact hM σ hσ
  -- Apply model_existence in L[[M]]
  obtain ⟨N, hStrN, hCountN, hModel'⟩ :=
    model_existence (trueInModelConsistencyPropertyEq M ι) T' hM' hT'_countable
  -- Restrict N to L
  letI : L.Structure N := (L.lhomWithConstants M).reduct N
  exact ⟨N, inferInstance, hCountN, by
    intro σ hσ
    have h := hModel' (σ.mapLanguage (L.lhomWithConstants M)) ⟨σ, hσ, rfl⟩
    simp only [Sentenceω.Realize] at h ⊢
    rwa [BoundedFormulaω.realize_mapLanguage] at h⟩

end Language

end FirstOrder
