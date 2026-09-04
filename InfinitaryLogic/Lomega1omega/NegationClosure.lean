/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Fragment

/-!
# Negation closure of a set of formulas

`Fragment.negationClosure S` is the smallest fragment containing `S` that is also closed under
formal negation `φ ↦ φ.not`.  It is an external syntactic operator on sets, placed beside
`Fragment.generated`: `Fragment` itself gains no field, in keeping with the frozen fragment
audit, which keeps formal-negation closure out of the structure.  `Fragment.NegationClosed` is
the corresponding predicate on fragments.

Countability is by the same finite-path encoding as `Fragment.generated`, with one extra step
tag for negation (private scaffolding; only `negationClosure_countable` is published).
-/

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

namespace Fragment

/-- A fragment closed under formal negation. -/
def NegationClosed (A : Fragment L) : Prop :=
  ∀ {n : ℕ} {φ : L.BoundedFormulaω Empty n},
    (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A → ⟨n, φ.not⟩ ∈ A

theorem negationClosed_top : (Fragment.top : Fragment L).NegationClosed := fun _ => Set.mem_univ _

/-- Component-and-negation closure of a set of formulas, as an inductive reachability
predicate: the rules of `GeneratedFrom` plus formal negation. -/
inductive NegationClosedFrom (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    (Σ n, L.BoundedFormulaω Empty n) → Prop
  | base {p} (h : p ∈ S) : NegationClosedFrom S p
  | imp_left {n : ℕ} {φ ψ : L.BoundedFormulaω Empty n} :
      NegationClosedFrom S ⟨n, φ.imp ψ⟩ → NegationClosedFrom S ⟨n, φ⟩
  | imp_right {n : ℕ} {φ ψ : L.BoundedFormulaω Empty n} :
      NegationClosedFrom S ⟨n, φ.imp ψ⟩ → NegationClosedFrom S ⟨n, ψ⟩
  | all_body {n : ℕ} {φ : L.BoundedFormulaω Empty (n + 1)} :
      NegationClosedFrom S ⟨n, φ.all⟩ → NegationClosedFrom S ⟨n + 1, φ⟩
  | iInf_comp {n : ℕ} {φs : ℕ → L.BoundedFormulaω Empty n} (k : ℕ) :
      NegationClosedFrom S ⟨n, BoundedFormulaω.iInf φs⟩ → NegationClosedFrom S ⟨n, φs k⟩
  | iSup_comp {n : ℕ} {φs : ℕ → L.BoundedFormulaω Empty n} (k : ℕ) :
      NegationClosedFrom S ⟨n, BoundedFormulaω.iSup φs⟩ → NegationClosedFrom S ⟨n, φs k⟩
  | neg {n : ℕ} {φ : L.BoundedFormulaω Empty n} :
      NegationClosedFrom S ⟨n, φ⟩ → NegationClosedFrom S ⟨n, φ.not⟩

/-- **The negation closure**: the smallest negation-closed fragment containing `S`. -/
def negationClosure (S : Set (Σ n, L.BoundedFormulaω Empty n)) : Fragment L where
  toSet := {p | NegationClosedFrom S p}
  imp_left_mem h := .imp_left h
  imp_right_mem h := .imp_right h
  all_mem h := .all_body h
  iInf_mem h k := .iInf_comp k h
  iSup_mem h k := .iSup_comp k h

theorem subset_negationClosure (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    S ⊆ (negationClosure S).toSet := fun _ h => .base h

theorem negationClosed_negationClosure (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    (negationClosure S).NegationClosed := fun h => .neg h

theorem generated_le_negationClosure (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    generated S ≤ negationClosure S :=
  generated_le_iff.mpr (subset_negationClosure S)

/-- The negation closure is below every negation-closed fragment containing `S`. -/
theorem negationClosure_le {S : Set (Σ n, L.BoundedFormulaω Empty n)} {A : Fragment L}
    (hSA : S ⊆ A.toSet) (hA : A.NegationClosed) : (negationClosure S).toSet ⊆ A.toSet := by
  intro p hp
  induction hp with
  | base h => exact hSA h
  | imp_left _ ih => exact A.imp_left_mem ih
  | imp_right _ ih => exact A.imp_right_mem ih
  | all_body _ ih => exact A.all_mem ih
  | iInf_comp k _ ih => exact A.iInf_mem ih k
  | iSup_comp k _ ih => exact A.iSup_mem ih k
  | neg _ ih => exact hA ih

/-- A negation-closed fragment is its own negation closure. -/
theorem negationClosure_toSet_eq {A : Fragment L} (hA : A.NegationClosed) :
    negationClosure A.toSet = A :=
  ext fun _ => ⟨fun h => negationClosure_le subset_rfl hA h, fun h => subset_negationClosure _ h⟩

/-! ### Countability: the closure-path encoding

`closureStep` extends `componentStep` by the tag `5` for negation; the rest is the argument of
`Fragment.generated_countable` verbatim.  The scaffolding is private: only
`negationClosure_countable` is consumed. -/

/-- One closure step, coded by a pair (tag, index): tag `5` is negation, the rest is
`componentStep`. -/
private def closureStep (p : Σ n, L.BoundedFormulaω Empty n) :
    ℕ × ℕ → Option (Σ n, L.BoundedFormulaω Empty n)
  | (5, _) => some ⟨p.1, p.2.not⟩
  | c => componentStep p c

/-- Iterated closure steps along a list of codes. -/
private def closurePath (p : Σ n, L.BoundedFormulaω Empty n) :
    List (ℕ × ℕ) → Option (Σ n, L.BoundedFormulaω Empty n)
  | [] => some p
  | c :: l => (closureStep p c).bind (closurePath · l)

private theorem closurePath_append (p : Σ n, L.BoundedFormulaω Empty n) (l₁ l₂ : List (ℕ × ℕ)) :
    closurePath p (l₁ ++ l₂) = (closurePath p l₁).bind (closurePath · l₂) := by
  induction l₁ generalizing p with
  | nil => rfl
  | cons c l ih =>
    show (closureStep p c).bind (closurePath · (l ++ l₂))
      = ((closureStep p c).bind (closurePath · l)).bind (closurePath · l₂)
    cases closureStep p c with
    | none => rfl
    | some q => exact ih q

/-- A single component step lands inside the closure. -/
private theorem NegationClosedFrom.of_componentStep {S : Set (Σ n, L.BoundedFormulaω Empty n)}
    {q p : Σ n, L.BoundedFormulaω Empty n} {c : ℕ × ℕ}
    (hq : NegationClosedFrom S q) (h : componentStep q c = some p) : NegationClosedFrom S p := by
  unfold componentStep at h
  split at h
  · exact Option.some_injective _ h ▸ hq.imp_left
  · exact Option.some_injective _ h ▸ hq.imp_right
  · exact Option.some_injective _ h ▸ hq.all_body
  · exact Option.some_injective _ h ▸ hq.iInf_comp _
  · exact Option.some_injective _ h ▸ hq.iSup_comp _
  · simp at h

/-- A single closure step lands inside the closure. -/
private theorem NegationClosedFrom.of_closureStep {S : Set (Σ n, L.BoundedFormulaω Empty n)}
    {q p : Σ n, L.BoundedFormulaω Empty n} {c : ℕ × ℕ}
    (hq : NegationClosedFrom S q) (h : closureStep q c = some p) : NegationClosedFrom S p := by
  obtain ⟨n, φ⟩ := q
  unfold closureStep at h
  split at h
  · exact Option.some_injective _ h ▸ hq.neg
  · exact hq.of_componentStep h

/-- **The path characterization**: the negation closure is exactly what is reachable from `S`
by finitely many coded closure steps. -/
private theorem negationClosedFrom_iff_path {S : Set (Σ n, L.BoundedFormulaω Empty n)}
    {p : Σ n, L.BoundedFormulaω Empty n} :
    NegationClosedFrom S p ↔ ∃ s ∈ S, ∃ l : List (ℕ × ℕ), closurePath s l = some p := by
  constructor
  · intro hp
    induction hp with
    | base h => exact ⟨_, h, [], rfl⟩
    | @imp_left n φ ψ _ ih =>
      obtain ⟨s, hs, l, hl⟩ := ih
      exact ⟨s, hs, l ++ [(0, 0)], by rw [closurePath_append, hl]; rfl⟩
    | @imp_right n φ ψ _ ih =>
      obtain ⟨s, hs, l, hl⟩ := ih
      exact ⟨s, hs, l ++ [(1, 0)], by rw [closurePath_append, hl]; rfl⟩
    | @all_body n φ _ ih =>
      obtain ⟨s, hs, l, hl⟩ := ih
      exact ⟨s, hs, l ++ [(2, 0)], by rw [closurePath_append, hl]; rfl⟩
    | @iInf_comp n φs k _ ih =>
      obtain ⟨s, hs, l, hl⟩ := ih
      exact ⟨s, hs, l ++ [(3, k)], by rw [closurePath_append, hl]; rfl⟩
    | @iSup_comp n φs k _ ih =>
      obtain ⟨s, hs, l, hl⟩ := ih
      exact ⟨s, hs, l ++ [(4, k)], by rw [closurePath_append, hl]; rfl⟩
    | @neg n φ _ ih =>
      obtain ⟨s, hs, l, hl⟩ := ih
      exact ⟨s, hs, l ++ [(5, 0)], by rw [closurePath_append, hl]; rfl⟩
  · rintro ⟨s, hs, l, hl⟩
    have hgen : ∀ (l : List (ℕ × ℕ)) (q : Σ n, L.BoundedFormulaω Empty n),
        NegationClosedFrom S q → closurePath q l = some p → NegationClosedFrom S p := by
      intro l
      induction l with
      | nil => exact fun q hq hl => Option.some_injective _ hl ▸ hq
      | cons c l ih =>
        intro q hq hl
        show NegationClosedFrom S p
        rw [show closurePath q (c :: l) = (closureStep q c).bind (closurePath · l)
          from rfl] at hl
        cases hstep : closureStep q c with
        | none => rw [hstep] at hl; exact absurd hl (by simp)
        | some r =>
          rw [hstep] at hl
          exact ih r (hq.of_closureStep hstep) hl
    exact hgen l s (.base hs) hl

/-- **Countability**: the negation closure of a countable set is countable. -/
theorem negationClosure_countable {S : Set (Σ n, L.BoundedFormulaω Empty n)}
    (hS : S.Countable) : (negationClosure S).toSet.Countable := by
  have hchar : (negationClosure S).toSet
      = ⋃ s ∈ S, Option.some ⁻¹' Set.range (fun l : List (ℕ × ℕ) => closurePath s l) := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_range]
    exact negationClosedFrom_iff_path.trans (by
      constructor
      · rintro ⟨s, hs, l, hl⟩; exact ⟨s, hs, l, hl⟩
      · rintro ⟨s, hs, l, hl⟩; exact ⟨s, hs, l, hl⟩)
  rw [hchar]
  exact Set.Countable.biUnion hS fun s _ =>
    (Set.countable_range _).preimage (Option.some_injective _)

end Fragment

end Language

end FirstOrder
