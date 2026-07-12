/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.Interpolation.ConsistencyPropertyEqOn

/-!
# Fair enumeration for a fragment-relative consistency property (issue #8 tranche 2, commit 3)

Generic over a universe `U` and a `ConsistencyPropertyEqOn U`: a finite consistent `S₀ ⊆ U`
extends to a Henkin-complete `S* ⊇ S₀`. The schedule is a **prefix sweep** — `stage (n+1)`
processes requests `0,…,n` starting from `stage n` — so, given a surjection `e : ℕ → Request U`,
each request `e k` is processed during every sweep after `k` (fairness with no arithmetic about
`Nat.pair`), while each sweep adds only finitely many sentences.

Branching / witness rules make a classical choice at the moment the request fires; the
triggering sentence stays present, so re-processing is harmless. The union `S*` is never claimed
to be in `C.sets` (Finding 1) — only that each closure target cohabits a later stage.

Named lemmas exposed for the inseparable-pair instance and the limit proof: the schedule
(`stage_mono`, `subset_stage`, `stage_subset_U`; stage-in-`C.sets` is automatic via the `SetIn`
subtype), the firing API (`request_fires_after` — every request fires in a sweep after any given
stage, via `beforeRequest`/`process_beforeRequest_eq_sweep`/`sweep_mono`), and finite-stage
preservation (`finite_stage`).

The remaining piece (the `HenkinComplete Sstar` acceptance theorem) is the per-field limit proof;
it consumes `request_fires_after` plus per-request "what `process` adds" facts.
-/

namespace FirstOrder.Language

open FirstOrder Structure Classical

variable {L : Language.{0, 0}} {U : Set L[[ℕ]].Sentenceω}

/-- A scheduling request. Decomposition rules dispatch on the trigger's outermost shape; `idx`
supplies the per-index parameter (component / instance / which negated-implication conclusion)
and is ignored by the classical-choice rules. -/
inductive Request (U : Set L[[ℕ]].Sentenceω) where
  | decompose (t : U) (idx : ℕ)
  | eqRefl (c : ℕ)
  | eqSymm (a b : ℕ)
  | eqTrans (a b d : ℕ)
  | relCongr (l : ℕ) (R : L.Relations l) (g : Fin l → ℕ) (i : Fin l) (b : ℕ)

namespace Request

/-- The request type is countable when `U` and the relation symbols are. -/
instance instCountable [Countable U] [Countable (Σ l, L.Relations l)] :
    Countable (Request U) := by
  haveI : ∀ l, Countable (L.Relations l) := countable_relations_each
  let f : Request U → (U × ℕ) ⊕ ℕ ⊕ (ℕ × ℕ) ⊕ (ℕ × ℕ × ℕ) ⊕
      (Σ l, L.Relations l × (Fin l → ℕ) × Fin l × ℕ) :=
    fun r => match r with
      | .decompose t idx => .inl (t, idx)
      | .eqRefl c => .inr (.inl c)
      | .eqSymm a b => .inr (.inr (.inl (a, b)))
      | .eqTrans a b d => .inr (.inr (.inr (.inl (a, b, d))))
      | .relCongr l R g i b => .inr (.inr (.inr (.inr ⟨l, R, g, i, b⟩)))
  have hf : Function.Injective f := by
    intro r₁ r₂ h
    cases r₁ <;> cases r₂ <;>
      simp only [f, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
        Sigma.mk.injEq] at h
    · obtain ⟨rfl, rfl⟩ := h; rfl
    · obtain rfl := h; rfl
    · obtain ⟨rfl, rfl⟩ := h; rfl
    · obtain ⟨rfl, rfl, rfl⟩ := h; rfl
    · obtain ⟨rfl, h⟩ := h
      rw [heq_eq_eq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl
  exact hf.countable

end Request

/-! ## One processing step -/

/-- A member of the consistency family, bundled with its membership proof. -/
abbrev SetIn (P : ConsistencyPropertyEqOn U) := {T : Set L[[ℕ]].Sentenceω // T ∈ P.sets}

variable {P : ConsistencyPropertyEqOn U}

/-- Process a decomposition request: if the trigger `t` is present, add the target dictated by
its outermost shape (the per-index rules use `idx`; the branching/witness rules choose
classically). -/
noncomputable def processDecompose (S : SetIn P) (t : U) (idx : ℕ) : SetIn P :=
  if hs : (t : L[[ℕ]].Sentenceω) ∈ S.1 then
    match heq : (t : L[[ℕ]].Sentenceω) with
    | .imp (.imp φ ψ) .falsum =>
      -- C1' (also subsumes C2 double-negation when `ψ = falsum`): add `φ` or `ψ.not`.
      have hmem : ((φ.imp ψ).imp BoundedFormulaω.falsum) ∈ S.1 := heq ▸ hs
      if idx = 0 then ⟨S.1 ∪ {φ}, (P.C1_neg_imp S.1 S.2 φ ψ hmem).1⟩
      else ⟨S.1 ∪ {ψ.not}, (P.C1_neg_imp S.1 S.2 φ ψ hmem).2⟩
    | .imp (.iInf φs) .falsum =>
      -- C3': choose a component whose negation stays consistent.
      have hmem : ((BoundedFormulaω.iInf φs).imp BoundedFormulaω.falsum) ∈ S.1 := heq ▸ hs
      let h := P.C3_neg_iInf S.1 S.2 φs hmem
      ⟨S.1 ∪ {(φs h.choose).not}, h.choose_spec⟩
    | .imp (.iSup φs) .falsum =>
      -- C4': every component's negation is consistent; add the `idx`-th.
      have hmem : ((BoundedFormulaω.iSup φs).imp BoundedFormulaω.falsum) ∈ S.1 := heq ▸ hs
      ⟨S.1 ∪ {(φs idx).not}, P.C4_neg_iSup S.1 S.2 φs hmem idx⟩
    | .imp (.all φ) .falsum =>
      -- negated universal: choose a witness.
      have hmem : ((BoundedFormulaω.all φ).imp BoundedFormulaω.falsum) ∈ S.1 := heq ▸ hs
      let h := P.neg_all_witness S.1 S.2 φ hmem
      ⟨S.1 ∪ {(instConst h.choose φ).not}, h.choose_spec⟩
    | .imp φ ψ =>
      -- C1: add whichever branch is consistent.
      have hmem : (φ.imp ψ) ∈ S.1 := heq ▸ hs
      if hb : S.1 ∪ {φ.not} ∈ P.sets then ⟨S.1 ∪ {φ.not}, hb⟩
      else ⟨S.1 ∪ {ψ}, (P.C1_imp S.1 S.2 φ ψ hmem).resolve_left hb⟩
    | .iInf φs =>
      have hmem : (BoundedFormulaω.iInf φs) ∈ S.1 := heq ▸ hs
      ⟨S.1 ∪ {φs idx}, P.C3_iInf S.1 S.2 φs hmem idx⟩
    | .iSup φs =>
      have hmem : (BoundedFormulaω.iSup φs) ∈ S.1 := heq ▸ hs
      let h := P.C4_iSup S.1 S.2 φs hmem
      ⟨S.1 ∪ {φs h.choose}, h.choose_spec⟩
    | .all φ =>
      have hmem : (BoundedFormulaω.all φ) ∈ S.1 := heq ▸ hs
      ⟨S.1 ∪ {instConst idx φ}, P.all_inst S.1 S.2 φ hmem idx⟩
    | _ => S
  else S

/-- Process one request. -/
noncomputable def process (S : SetIn P) : Request U → SetIn P
  | .decompose t idx => processDecompose S t idx
  | .eqRefl c => ⟨S.1 ∪ {constEq c c}, P.eq_refl S.1 S.2 c⟩
  | .eqSymm a b =>
    if h : constEq a b ∈ S.1 then ⟨S.1 ∪ {constEq b a}, P.eq_symm S.1 S.2 a b h⟩ else S
  | .eqTrans a b d =>
    if h : constEq a b ∈ S.1 ∧ constEq b d ∈ S.1 then
      ⟨S.1 ∪ {constEq a d}, P.eq_trans S.1 S.2 a b d h.1 h.2⟩ else S
  | .relCongr l R g i b =>
    if h : relInst R g ∈ S.1 ∧ constEq (g i) b ∈ S.1 then
      ⟨S.1 ∪ {relInst R (Function.update g i b)}, P.rel_congr S.1 S.2 l R g i b h.1 h.2⟩ else S

/-- Processing only grows the set (`processDecompose`). -/
theorem subset_processDecompose (S : SetIn P) (t : U) (idx : ℕ) :
    S.1 ⊆ (processDecompose S t idx).1 := by
  unfold processDecompose
  split
  · split <;> (try split) <;>
      first | exact Set.subset_union_left | exact subset_rfl
  · exact subset_rfl

/-- Processing only grows the set. -/
theorem subset_process (S : SetIn P) (r : Request U) : S.1 ⊆ (process S r).1 := by
  cases r with
  | decompose t idx => exact subset_processDecompose S t idx
  | eqRefl c => exact Set.subset_union_left
  | eqSymm a b =>
    simp only [process]; split_ifs <;> first | exact Set.subset_union_left | exact subset_rfl
  | eqTrans a b d =>
    simp only [process]; split_ifs <;> first | exact Set.subset_union_left | exact subset_rfl
  | relCongr l R g i b =>
    simp only [process]; split_ifs <;> first | exact Set.subset_union_left | exact subset_rfl

/-! ## The prefix-sweep schedule -/

variable (e : ℕ → Request U)

/-- One sweep: process requests `e 0, …, e n` in order. -/
noncomputable def sweep (S : SetIn P) : ℕ → SetIn P
  | 0 => process S (e 0)
  | (n + 1) => process (sweep S n) (e (n + 1))

/-- `stage (n+1)` processes requests `0,…,n` starting from `stage n`. -/
noncomputable def stage (S₀ : SetIn P) : ℕ → SetIn P
  | 0 => S₀
  | (n + 1) => sweep e (stage S₀ n) n

theorem subset_sweep (S : SetIn P) (n : ℕ) : S.1 ⊆ (sweep e S n).1 := by
  induction n with
  | zero => exact subset_process S (e 0)
  | succ n ih => exact ih.trans (subset_process (sweep e S n) (e (n + 1)))

/-- **Stage monotonicity** (one step). -/
theorem stage_subset_succ (S₀ : SetIn P) (n : ℕ) : (stage e S₀ n).1 ⊆ (stage e S₀ (n + 1)).1 :=
  subset_sweep e (stage e S₀ n) n

/-- **Stage monotonicity**. -/
theorem stage_mono (S₀ : SetIn P) {m n : ℕ} (h : m ≤ n) :
    (stage e S₀ m).1 ⊆ (stage e S₀ n).1 := by
  induction n with
  | zero => rw [Nat.le_zero.mp h]
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | rfl
    · exact (ih (Nat.lt_succ_iff.mp h')).trans (stage_subset_succ e S₀ n)
    · exact subset_rfl

/-- **`S₀ ⊆` every stage**. -/
theorem subset_stage (S₀ : SetIn P) (n : ℕ) : S₀.1 ⊆ (stage e S₀ n).1 :=
  stage_mono e S₀ (Nat.zero_le n)

/-- **Each stage lies in `U`**. -/
theorem stage_subset_U (S₀ : SetIn P) (n : ℕ) : (stage e S₀ n).1 ⊆ U :=
  P.subset_U _ (stage e S₀ n).2

/-- **The limit** of the enumeration. -/
noncomputable def Sstar (S₀ : SetIn P) : Set L[[ℕ]].Sentenceω := ⋃ n, (stage e S₀ n).1

theorem subset_Sstar (S₀ : SetIn P) : S₀.1 ⊆ Sstar e S₀ :=
  fun x hx => Set.mem_iUnion.mpr ⟨0, hx⟩

theorem Sstar_subset_U (S₀ : SetIn P) : Sstar e S₀ ⊆ U :=
  Set.iUnion_subset fun n => stage_subset_U e S₀ n

theorem mem_Sstar_iff (S₀ : SetIn P) {x : L[[ℕ]].Sentenceω} :
    x ∈ Sstar e S₀ ↔ ∃ n, x ∈ (stage e S₀ n).1 := Set.mem_iUnion

/-! ## The firing API -/

/-- The accumulated set just before request `e k` is processed in a sweep from `S`. -/
noncomputable def beforeRequest (S : SetIn P) : ℕ → SetIn P
  | 0 => S
  | (k + 1) => sweep e S k

theorem subset_beforeRequest (S : SetIn P) (k : ℕ) : S.1 ⊆ (beforeRequest e S k).1 := by
  cases k with
  | zero => exact subset_rfl
  | succ k => exact subset_sweep e S k

/-- Processing `e k` at its accumulated point advances the sweep by one — nearly definitional. -/
theorem process_beforeRequest_eq_sweep (S : SetIn P) (k : ℕ) :
    process (beforeRequest e S k) (e k) = sweep e S k := by
  cases k <;> rfl

/-- Sweeps are monotone in the number of requests processed. -/
theorem sweep_mono (S : SetIn P) {k n : ℕ} (h : k ≤ n) : (sweep e S k).1 ⊆ (sweep e S n).1 := by
  induction n with
  | zero => rw [Nat.le_zero.mp h]
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | rfl
    · exact (ih (Nat.lt_succ_iff.mp h')).trans (subset_process (sweep e S n) (e (n + 1)))
    · exact subset_rfl

/-- **The firing consumer lemma** (fairness): for a surjective schedule, every request fires in
some sweep after any given stage `m` — the pre-accumulator contains `stage m`, and the process
output at the firing lands inside `stage (n+1)`. -/
theorem request_fires_after (he : Function.Surjective e) (S₀ : SetIn P) (r : Request U) (m : ℕ) :
    ∃ n, m ≤ n ∧ ∃ acc : SetIn P,
      (stage e S₀ m).1 ⊆ acc.1 ∧ (process acc r).1 ⊆ (stage e S₀ (n + 1)).1 := by
  obtain ⟨k, rfl⟩ := he r
  refine ⟨max m k, le_max_left m k, beforeRequest e (stage e S₀ (max m k)) k,
    (stage_mono e S₀ (le_max_left m k)).trans (subset_beforeRequest e _ k), ?_⟩
  rw [process_beforeRequest_eq_sweep]
  exact sweep_mono e (stage e S₀ (max m k)) (le_max_right m k)

/-! ## Finite-stage preservation -/

theorem finite_processDecompose {S : SetIn P} (t : U) (idx : ℕ) (hS : S.1.Finite) :
    (processDecompose S t idx).1.Finite := by
  unfold processDecompose
  split
  · split <;> (try split) <;>
      first | exact hS.union (Set.finite_singleton _) | exact hS
  · exact hS

theorem finite_process {S : SetIn P} (r : Request U) (hS : S.1.Finite) : (process S r).1.Finite := by
  cases r with
  | decompose t idx => exact finite_processDecompose t idx hS
  | eqRefl c => exact hS.union (Set.finite_singleton _)
  | eqSymm a b => simp only [process]; split_ifs <;> first | exact hS.union (Set.finite_singleton _) | exact hS
  | eqTrans a b d => simp only [process]; split_ifs <;> first | exact hS.union (Set.finite_singleton _) | exact hS
  | relCongr l R g i b =>
    simp only [process]; split_ifs <;> first | exact hS.union (Set.finite_singleton _) | exact hS

theorem finite_sweep {S : SetIn P} (hS : S.1.Finite) (n : ℕ) : (sweep e S n).1.Finite := by
  induction n with
  | zero => exact finite_process (e 0) hS
  | succ n ih => exact finite_process (e (n + 1)) ih

/-- **Finite-stage preservation**: from a finite initial set, every stage is finite (documenting
that the construction stays inside the finite-pair instance). -/
theorem finite_stage {S₀ : SetIn P} (hS₀ : S₀.1.Finite) (n : ℕ) : (stage e S₀ n).1.Finite := by
  induction n with
  | zero => exact hS₀
  | succ n ih => exact finite_sweep e ih n

end FirstOrder.Language
