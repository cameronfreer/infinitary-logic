/-
Regression guard for uniform fixation under stage projections
(`InfinitaryLogic/UniformFixation.lean`).

Every public theorem is *applied*, not only listed for its axioms.  The concrete projection
system is truncation on the countable ordinals: labels `CO = Set.Iio ω₁` (as a subtype),
`project α i = min α i`, so the label rank of `i` is `i` itself.

* **The API on the truncation system.**  The projection law normalizes by `simp` (idempotence and
  triple compositions); the bundled and law-only label-rank lemmas agree; rank and fixedness are
  dual (`exists_labelRank_gt_iff`: every countable stage is exceeded by some label rank).

* **(R1) Empty coordinates.**  Every presentation is fixed at `0`; the explicit stage
  `⨆ c, (α c + 1)` is `0` and Theorem 2's explicit form fixes at `0`; Theorem 2 applies with a
  vacuous eventual-invariance premise; the least fixing stage of Theorem 1 is `0`.
* **(R2) `C = ℕ`**, admissible presentations only at finite stages `m`, coordinate `n` carrying
  `min m n`; coordinate `n` has its own witness presentation at stage `n` (distinct coordinates,
  distinct witnesses).  No presentation is admissible at `ω`.  The uniform stages are exactly the
  `A ≥ ω`; the explicit stage of the witnesses is `ω` (both the `⨆ (α + 1)` and the `⨆ α`
  forms); realized label ranks are `min m n`; the classwise label-rank bounds are exactly the
  `A ≥ ω`; the least simultaneous fixing stage of the labels `n ↦ n` is `ω`, and leastness of
  `⨆ n, labelRank (ℓ n)` holds on the law-only structure for every admissible presentation
  (`forall_fixed_iff_iSup_labelRank_le_of_exists`, premise from stage correctness).
* **(R3) Negative, uncountable `C = Iio ω₁`.**  Stage correctness and eventual invariance hold,
  yet there is no countable uniform stage, no countable fixing stage of the identity
  presentation (Theorem 1 fails) and no countable classwise label-rank bound; so the coordinate
  type is not countable (countability is load-bearing).
* **(R4) Negative, stage correctness dropped.**  Every presentation admissible at stage `0`:
  eventual invariance holds vacuously above `0`, stage correctness fails, and no uniform stage
  exists.
* **(R5) `A` is independent of `β` and `ℓ`.**  One stage `ω` fixes presentations at different
  stages, and it is the explicit stage of the witnesses.
* **The contract's premise forms.**  Unguarded stage correctness implies the guarded premise,
  and the eventual-agreement premise with binder order `∀ β ℓ, α < β → β < ω₁ → Adm β ℓ → ...`
  is equivalent to `EventuallyInvariant`.
* **The label rank needs a premise.**  For the constant projection to `false` on `Bool`, the
  label `true` is fixed at no stage: its label rank is the junk value `0`, and the
  `labelRank_le_iff` shape fails for it.  The fixing rank of a coordinate in a presentation is
  the label rank of its label by `rfl`, so no separate presentation rank exists.

Two separate tests about the eventual-invariance premise, which must not be conflated:

* **(W1) Quantifier order: uniformity ACROSS PRESENTATIONS.**  With the swapped order
  `∀ c ∀ β ℓ ∃ α_c ℓ_c` the premise holds trivially for a ladder of presentations whose label at
  stage `β` is `β`, and no uniform stage exists: `¬ SwappedOrderStatement`, even under global
  eventual fixation.  This shows that the order `∀ c ∃ α_c ℓ_c ∀ β ℓ` is what makes the stage
  uniform across presentations; it does not by itself show that the admissible witness is needed.
* **(W2) The admissible witness pins the EXPLICIT bound.**  With only a bare eventual value
  (label `2` after threshold `0`, where no presentation is admissible), a uniform stage still
  exists (`exists_uniform_fixing_stage_of_eventually_const`; the explicit eventual-value stage,
  here `2`, countable in the bundled `uniform_fixing_of_eventual_values` and also reached by the
  law-only version), but the formula `⨆ c, (α_c + 1) = 1` is NOT a uniform stage.  Existence
  alone does not need the witness.

* **Import closure.**  The `InfinitaryLogic` closure of the module is exactly `UniformFixation`,
  `OrdinalCountability` and `OrdinalUtil` (`[CLOSURE DRIFT]` otherwise), with no `Scott`,
  `Descriptive`, `ModelTheory`, `Karp` or `Lomega1omega` module.

Every declaration of the module (enumerated from the environment, and a fixed list that must
be present) and every declaration of this guard uses only the standard axioms.  The closure
check and the axiom audit run in one command, so the OK line is printed only when both pass.

Run with: lake env lean scripts/check_uniform_fixation_regressions.lean
-/
import InfinitaryLogic.UniformFixation

open Lean InfinitaryLogic Set

universe u v

noncomputable section

namespace UniformFixationGuard

open StageProjection

/-! ### Truncation on the countable ordinals -/

/-- Countable ordinals as labels. -/
abbrev CO : Type 1 := {x : Ordinal.{0} // x < Ordinal.omega 1}

/-- Truncation: `project α i = min α i`; every label `i` is fixed at the stage `i`. -/
def P : CountablyFixedProjection CO where
  project α i := ⟨min α i.1, (min_le_right _ _).trans_lt i.2⟩
  project_project α β i := Subtype.ext (min_assoc α β i.1).symm
  eventually_fixed i := ⟨i.1, i.2, Subtype.ext (min_self i.1)⟩

theorem P_fixed_iff {α : Ordinal.{0}} {i : CO} : P.project α i = i ↔ i.1 ≤ α := by
  -- `P.project α i` is the subtype element `⟨min α i.1, _⟩` by definition of `P`.
  change (⟨min α i.1, _⟩ : CO) = i ↔ _
  rw [Subtype.ext_iff]
  exact min_eq_right_iff

theorem succ_lt_omega1 {a : Ordinal.{0}} (h : a < Ordinal.omega 1) : a + 1 < Ordinal.omega 1 :=
  (Cardinal.isSuccLimit_omega 1).add_one_lt h

/-- No stage `A` fixes the label `A + 1`. -/
theorem P_not_fixed_succ (A : Ordinal.{0}) (h : A + 1 < Ordinal.omega 1) :
    P.project A ⟨A + 1, h⟩ ≠ ⟨A + 1, h⟩ := fun he ↦
  (lt_add_one A).not_ge (P_fixed_iff.mp he)

/-- The label rank of `i` is `i`. -/
theorem P_labelRank (i : CO) : P.labelRank i = i.1 :=
  le_antisymm (labelRank_le_of_fixed (P_fixed_iff.mpr le_rfl))
    (P_fixed_iff.mp (P.fixed_labelRank i))

/-- The parent-level and bundled label-rank API agree on `P`. -/
theorem P_labelRank_api (i : CO) (α : Ordinal.{0}) :
    (P.labelRank i ≤ α ↔ P.project α i = i) ∧
      (P.labelRank i ≤ α ↔ P.project α i = i) ∧ P.labelRank i < Ordinal.omega 1 ∧
      (⋃ α < Ordinal.omega 1, {i : CO | P.project α i = i}) = Set.univ :=
  ⟨P.labelRank_le_iff, labelRank_le_iff_of_exists ⟨_, P.fixed_labelRank i⟩,
    P.labelRank_lt_omega1 i, P.iUnion_fixedLabels_eq_univ⟩

/-- The projection law is a `simp` lemma: idempotence and triple compositions normalize. -/
theorem simp_law (S : StageProjection CO) (α β γ : Ordinal.{0}) (i : CO) :
    S.project α (S.project α i) = S.project α i ∧
      S.project α (S.project β (S.project γ i)) = S.project (min α (min β γ)) i := by
  simp

/-- Rank and fixedness are dual: above every countable `A` some label has larger rank, and `A`
fails to fix some label. -/
theorem P_rank_gt (A : Ordinal.{0}) (hA : A < Ordinal.omega 1) :
    (∃ i, A < P.labelRank i) ∧ ∃ i, P.project A i ≠ i :=
  have h : ∃ i, P.project A i ≠ i := ⟨_, P_not_fixed_succ A (succ_lt_omega1 hA)⟩
  ⟨(P.exists_labelRank_gt_iff A).mpr h, h⟩

theorem natCast_lt_omega1 (n : ℕ) : (n : Ordinal.{0}) < Ordinal.omega 1 :=
  (Ordinal.natCast_lt_omega0 n).trans Ordinal.omega0_lt_omega_one

/-! ### (R1) Empty coordinates -/

theorem empty_fixed (I : Type u) (S : StageProjection I)
    (Adm : Ordinal.{0} → (Empty → I) → Prop) :
    ∀ β, β < Ordinal.omega 1 → ∀ ℓ, Adm β ℓ → S.FixedAt 0 ℓ :=
  fun _ _ _ _ c ↦ isEmptyElim c

theorem empty_explicit_bound (α : Empty → Ordinal.{0}) : (⨆ c, (α c + 1)) = 0 :=
  Ordinal.iSup_eq_zero_iff.mpr isEmptyElim

/-- Theorem 2's explicit form at empty `C` fixes at `0`. -/
theorem empty_explicit (I : Type u) (S : StageProjection I)
    (Adm : Ordinal.{0} → (Empty → I) → Prop)
    (hstage : ∀ α, α < Ordinal.omega 1 → ∀ ℓ, Adm α ℓ → S.FixedAt α ℓ) :
    ∀ β, β < Ordinal.omega 1 → ∀ ℓ, Adm β ℓ → S.FixedAt 0 ℓ := by
  have h := S.uniform_fixing_at_iSup_add_one_of_witnesses Adm hstage isEmptyElim isEmptyElim
    isEmptyElim isEmptyElim isEmptyElim
  rwa [empty_explicit_bound] at h

/-- Theorem 2 at empty `C`, the eventual-invariance premise vacuous. -/
theorem empty_uniform (I : Type u) (S : StageProjection I)
    (Adm : Ordinal.{0} → (Empty → I) → Prop)
    (hstage : ∀ α, α < Ordinal.omega 1 → ∀ ℓ, Adm α ℓ → S.FixedAt α ℓ) :
    ∃ A < Ordinal.omega 1, ∀ β, β < Ordinal.omega 1 → ∀ ℓ, Adm β ℓ → S.FixedAt A ℓ :=
  S.exists_uniform_fixing_stage Adm hstage isEmptyElim

/-- Theorem 1 at empty `C`: the least simultaneous fixing stage is `0`. -/
theorem empty_least (ℓ : Empty → CO) :
    (⨆ c, P.labelRank (ℓ c)) = 0 ∧ P.FixedAt 0 ℓ ∧ ∃ A < Ordinal.omega 1, P.FixedAt A ℓ :=
  ⟨Ordinal.iSup_eq_zero_iff.mpr isEmptyElim,
    (P.forall_fixed_iff_iSup_labelRank_le ℓ).mpr (Ordinal.iSup_eq_zero_iff.mpr isEmptyElim).le,
    P.exists_fixing_stage_of_countable ℓ⟩

/-! ### (R2) `C = ℕ`, witnesses at different stages -/

/-- The label `n`, fixed exactly from stage `n` on. -/
def natLabel (n : ℕ) : CO := ⟨n, natCast_lt_omega1 n⟩

/-- The presentation at finite stage `m`: coordinate `n` carries `min m n`. -/
def natPres (m : ℕ) : ℕ → CO := fun n ↦ natLabel (min m n)

/-- Admissible presentations live only at finite stages. -/
def natAdm (β : Ordinal.{0}) (ℓ : ℕ → CO) : Prop := ∃ m : ℕ, β = m ∧ ℓ = natPres m

theorem natAdm_stage : ∀ α, α < Ordinal.omega 1 → ∀ ℓ, natAdm α ℓ → P.FixedAt α ℓ := by
  rintro _ - _ ⟨m, rfl, rfl⟩ c
  exact P_fixed_iff.mpr (Nat.cast_le.mpr (min_le_left m c))

theorem natAdm_agree (n : ℕ) :
    ∀ β, (n : Ordinal.{0}) < β → β < Ordinal.omega 1 → ∀ ℓ, natAdm β ℓ → ℓ n = natPres n n := by
  rintro _ hlt - _ ⟨m, rfl, rfl⟩
  have hnm : n < m := Nat.cast_lt.mp hlt
  simp only [natPres, min_self, min_eq_right hnm.le]

/-- Coordinate `n` is eventually invariant with witness `natPres n` at stage `n`. -/
theorem natAdm_ev : ∀ c, EventuallyInvariant natAdm c :=
  fun n ↦ ⟨n, natCast_lt_omega1 n, natPres n, ⟨n, rfl, rfl⟩, natAdm_agree n⟩

theorem natPres_injective : Function.Injective natPres := by
  intro m k h
  have h1 := congrArg (fun ℓ ↦ (ℓ (max m k)).1) h
  simp only [natPres, natLabel, min_eq_left (le_max_left m k),
    min_eq_left (le_max_right m k), Nat.cast_inj] at h1
  exact h1

theorem natAdm_no_infinite_stage (ℓ : ℕ → CO) : ¬ natAdm Ordinal.omega0 ℓ := by
  rintro ⟨m, hm, -⟩
  exact (Ordinal.natCast_lt_omega0 m).ne hm.symm

theorem nat_uniform : ∃ A < Ordinal.omega 1, ∀ β, β < Ordinal.omega 1 → ∀ ℓ, natAdm β ℓ →
    P.FixedAt A ℓ :=
  P.exists_uniform_fixing_stage natAdm natAdm_stage natAdm_ev

/-- The uniform stages of the `ℕ` family are exactly the `A ≥ ω`. -/
theorem nat_uniform_iff (A : Ordinal.{0}) :
    (∀ β, β < Ordinal.omega 1 → ∀ ℓ, natAdm β ℓ → P.FixedAt A ℓ) ↔ Ordinal.omega0 ≤ A := by
  constructor
  · intro h
    refine Ordinal.omega0_le.mpr fun n ↦ ?_
    have := P_fixed_iff.mp (h n (natCast_lt_omega1 n) (natPres n) ⟨n, rfl, rfl⟩ n)
    simpa [natPres, natLabel] using this
  · rintro hA _ _ _ ⟨m, rfl, rfl⟩ c
    exact P_fixed_iff.mpr ((Ordinal.natCast_lt_omega0 _).le.trans hA)

theorem nat_explicit_bound : (⨆ n : ℕ, ((n : Ordinal.{0}) + 1)) = Ordinal.omega0 := by
  refine le_antisymm (Ordinal.iSup_le fun n ↦ ?_) (Ordinal.omega0_le.mpr fun n ↦ ?_)
  · exact_mod_cast (Ordinal.natCast_lt_omega0 (n + 1)).le
  · exact (lt_add_one (n : Ordinal.{0})).le.trans
      (Ordinal.le_iSup (fun n : ℕ ↦ (n : Ordinal.{0}) + 1) n)

/-- Both explicit forms of Theorem 2 give the stage `ω` for these witnesses, the least one:
`⨆ n, (n + 1) = ω` and `⨆ n, n = ω`. -/
theorem nat_explicit :
    (∀ β, β < Ordinal.omega 1 → ∀ ℓ, natAdm β ℓ → P.FixedAt Ordinal.omega0 ℓ) ∧
      (∀ β, β < Ordinal.omega 1 → ∀ ℓ, natAdm β ℓ → P.FixedAt Ordinal.omega0 ℓ) := by
  have h := P.uniform_fixing_at_iSup_add_one_of_witnesses natAdm natAdm_stage (fun n ↦ n)
    natCast_lt_omega1 natPres (fun n ↦ ⟨n, rfl, rfl⟩) natAdm_agree
  have h' := P.uniform_fixing_at_iSup_of_witnesses natAdm natAdm_stage (fun n ↦ n)
    natCast_lt_omega1 natPres (fun n ↦ ⟨n, rfl, rfl⟩) natAdm_agree
  rw [nat_explicit_bound] at h
  rw [Ordinal.iSup_natCast] at h'
  exact ⟨h, h'⟩

/-- Realized label ranks: coordinate `n` at stage `m` has rank `min m n`. -/
theorem nat_labelRank (m n : ℕ) : P.labelRank (natPres m n) = (min m n : ℕ) :=
  P_labelRank _

theorem nat_classwise_iff (A : Ordinal.{0}) :
    (∀ β, β < Ordinal.omega 1 → ∀ ℓ, natAdm β ℓ → ∀ c, P.labelRank (ℓ c) ≤ A) ↔
      Ordinal.omega0 ≤ A := by
  rw [← uniform_fixed_iff_labelRank_le natAdm_stage]
  exact nat_uniform_iff A

/-- The classwise label-rank bound, and the per-presentation forms. -/
theorem nat_classwise :
    (∃ A < Ordinal.omega 1, ∀ β, β < Ordinal.omega 1 → ∀ ℓ, natAdm β ℓ →
      ∀ c, P.labelRank (ℓ c) ≤ A) ∧ P.labelRank (natPres 3 7) ≤ ((3 : ℕ) : Ordinal.{0}) ∧
      P.labelRank (natPres 3 7) ≤ Ordinal.omega0 :=
  ⟨P.exists_classwise_labelRank_bound natAdm natAdm_stage natAdm_ev,
    labelRank_le_stage_of_adm natAdm_stage (natCast_lt_omega1 3) ⟨3, rfl, rfl⟩ 7,
    labelRank_le_of_adm nat_explicit.1 (natCast_lt_omega1 3) ⟨3, rfl, rfl⟩ 7⟩

/-- The least simultaneous fixing stage of `n ↦ n` is `ω` (Theorem 1 with leastness). -/
theorem nat_least_fixing_stage :
    (⨆ n, P.labelRank (natLabel n)) = Ordinal.omega0 ∧
      (⨆ n, P.labelRank (natLabel n)) < Ordinal.omega 1 ∧
      (∀ A, (∀ n, P.project A (natLabel n) = natLabel n) ↔ Ordinal.omega0 ≤ A) := by
  have h : (⨆ n, P.labelRank (natLabel n)) = Ordinal.omega0 := by
    simp only [P_labelRank, natLabel, Ordinal.iSup_natCast]
  refine ⟨h, P.iSup_labelRank_lt_omega1 natLabel, fun A ↦ ?_⟩
  rw [P.forall_fixed_iff_iSup_labelRank_le natLabel, h]

/-- The fixing rank of a coordinate in a presentation is the label rank, by `rfl`. -/
theorem presentation_rank_rfl (ℓ : ℕ → CO) (c : ℕ) :
    leastLevel (fun α ↦ {c : ℕ | P.project α (ℓ c) = ℓ c}) c = P.labelRank (ℓ c) :=
  rfl

/-- Leastness on the law-only structure: the least simultaneous fixing stage of the admissible
presentation at stage `m` is `⨆ n, labelRank (natPres m n) = m`. -/
theorem nat_least_law_only (m : ℕ) (A : Ordinal.{0}) :
    (∀ n, P.project A (natPres m n) = natPres m n) ↔
      (⨆ n, P.labelRank (natPres m n)) ≤ A :=
  P.toStageProjection.forall_fixed_iff_iSup_labelRank_le_of_exists (natPres m)
    fun n ↦ ⟨m, natAdm_stage m (natCast_lt_omega1 m) _ ⟨m, rfl, rfl⟩ n⟩

/-- Theorem 1 per coordinate, through the parent API. -/
theorem nat_theorem1 : ∃ A < Ordinal.omega 1, P.FixedAt A natLabel :=
  P.exists_fixing_stage_of_forall natLabel fun n ↦
    ⟨n, natCast_lt_omega1 n, P_fixed_iff.mpr le_rfl⟩

/-! ### (R5) One stage for presentations at different stages -/

theorem nat_shared (c : ℕ) :
    P.project Ordinal.omega0 (natPres 0 c) = natPres 0 c ∧
      P.project Ordinal.omega0 (natPres 5 c) = natPres 5 c :=
  ⟨nat_explicit.1 0 (natCast_lt_omega1 0) _ ⟨0, rfl, rfl⟩ c,
    nat_explicit.1 ((5 : ℕ) : Ordinal.{0}) (natCast_lt_omega1 5) _ ⟨5, rfl, rfl⟩ c⟩

/-! ### (R3) Negative: uncountable `C = Iio ω₁` -/

/-- The presentation at stage `β`: coordinate `c` carries `min β c`. -/
def coPres (β : Ordinal.{0}) : CO → CO := fun c ↦ P.project β c

def coAdm (β : Ordinal.{0}) (ℓ : CO → CO) : Prop := β < Ordinal.omega 1 ∧ ℓ = coPres β

theorem coAdm_stage : ∀ α, α < Ordinal.omega 1 → ∀ ℓ, coAdm α ℓ → P.FixedAt α ℓ := by
  rintro β - _ ⟨-, rfl⟩ c
  simp [coPres]

theorem coAdm_ev : ∀ c, EventuallyInvariant coAdm c := by
  intro c
  refine ⟨c.1, c.2, coPres c.1, ⟨c.2, rfl⟩, ?_⟩
  rintro β hlt - _ ⟨-, rfl⟩
  rw [coPres, coPres, P_fixed_iff.mpr hlt.le, P_fixed_iff.mpr le_rfl]

theorem co_no_uniform : ¬ ∃ A < Ordinal.omega 1, ∀ β, β < Ordinal.omega 1 → ∀ ℓ, coAdm β ℓ →
    P.FixedAt A ℓ := by
  rintro ⟨A, hA, h⟩
  have hA1 := succ_lt_omega1 hA
  have := h (A + 1) hA1 _ ⟨hA1, rfl⟩ ⟨A + 1, hA1⟩
  have hfix : P.project (A + 1) ⟨A + 1, hA1⟩ = ⟨A + 1, hA1⟩ := P_fixed_iff.mpr le_rfl
  rw [coPres, hfix] at this
  exact P_not_fixed_succ A hA1 this

/-- Countability is load-bearing: everything else of Theorem 2 holds for `C = Iio ω₁`. -/
theorem co_not_countable : ¬ Countable CO := fun _ ↦
  co_no_uniform (P.exists_uniform_fixing_stage coAdm coAdm_stage coAdm_ev)

/-- Theorem 1 fails for `C = Iio ω₁` and the identity presentation. -/
theorem co_no_fixing_stage : ¬ ∃ A < Ordinal.omega 1, P.FixedAt A (id : CO → CO) := by
  rintro ⟨A, hA, h⟩
  exact P_not_fixed_succ A (succ_lt_omega1 hA) (h _)

theorem co_no_classwise_bound : ¬ ∃ A < Ordinal.omega 1, ∀ β, β < Ordinal.omega 1 → ∀ ℓ,
    coAdm β ℓ → ∀ c, P.labelRank (ℓ c) ≤ A := by
  rintro ⟨A, hA, h⟩
  exact co_no_uniform ⟨A, hA, (uniform_fixed_iff_labelRank_le coAdm_stage).mpr h⟩

/-! ### (R4) Negative: stage correctness dropped -/

/-- Every presentation is admissible, but only at stage `0`. -/
def zeroAdm (β : Ordinal.{0}) (_ : Unit → CO) : Prop := β = 0

theorem zeroAdm_ev : ∀ c, EventuallyInvariant zeroAdm c :=
  fun _ ↦ ⟨0, Ordinal.omega_pos 1, fun _ ↦ ⟨0, Ordinal.omega_pos 1⟩, rfl,
    fun _ hlt _ _ h0 ↦ absurd h0 hlt.ne'⟩

theorem zeroAdm_not_stage :
    ¬ ∀ α, α < Ordinal.omega 1 → ∀ ℓ, zeroAdm α ℓ → P.FixedAt α ℓ := by
  intro h
  have h1 := succ_lt_omega1 (Ordinal.omega_pos 1)
  exact P_not_fixed_succ 0 h1 (h 0 (Ordinal.omega_pos 1) (fun _ ↦ ⟨0 + 1, h1⟩) rfl ())

theorem zeroAdm_no_uniform : ¬ ∃ A < Ordinal.omega 1, ∀ β, β < Ordinal.omega 1 → ∀ ℓ,
    zeroAdm β ℓ → P.FixedAt A ℓ := by
  rintro ⟨A, hA, h⟩
  have hA1 := succ_lt_omega1 hA
  exact P_not_fixed_succ A hA1 (h 0 (Ordinal.omega_pos 1) (fun _ ↦ ⟨A + 1, hA1⟩) rfl ())

/-! ### The contract's premise forms -/

/-- Unguarded stage correctness gives the guarded premise of Theorem 2. -/
theorem uniform_of_unguarded {I : Type u} {C : Type v} [Countable C] (S : StageProjection I)
    (Adm : Ordinal.{0} → (C → I) → Prop)
    (hcorrect : ∀ β ℓ, Adm β ℓ → ∀ c, S.project β (ℓ c) = ℓ c)
    (hev : ∀ c, EventuallyInvariant Adm c) :
    ∃ A < Ordinal.omega 1, ∀ β < Ordinal.omega 1, ∀ ℓ, Adm β ℓ → ∀ c, S.project A (ℓ c) = ℓ c :=
  S.exists_uniform_fixing_stage Adm (fun β _ ℓ h ↦ hcorrect β ℓ h) hev

/-- The eventual-agreement premise with binder order `∀ β ℓ` is `EventuallyInvariant`. -/
theorem eventuallyInvariant_iff {I : Type u} {C : Type v} (Adm : Ordinal.{0} → (C → I) → Prop)
    (c : C) : EventuallyInvariant Adm c ↔ ∃ α < Ordinal.omega 1, ∃ ℓ₀, Adm α ℓ₀ ∧
      ∀ β ℓ, α < β → β < Ordinal.omega 1 → Adm β ℓ → ℓ c = ℓ₀ c :=
  ⟨fun ⟨α, hα, ℓ₀, h₀, h⟩ ↦ ⟨α, hα, ℓ₀, h₀, fun β ℓ h1 h2 h3 ↦ h β h1 h2 ℓ h3⟩,
    fun ⟨α, hα, ℓ₀, h₀, h⟩ ↦ ⟨α, hα, ℓ₀, h₀, fun β h1 h2 ℓ h3 ↦ h β ℓ h1 h2 h3⟩⟩

/-! ### The label rank needs a premise -/

/-- Constant projection to `false`: the label `true` is fixed at no stage. -/
def constFalse : StageProjection Bool where
  project _ _ := false
  project_project _ _ _ := rfl

theorem junk_labelRank : constFalse.labelRank true = 0 ∧
    ¬ (constFalse.labelRank true ≤ 0 ↔ constFalse.project 0 true = true) := by
  have h : constFalse.labelRank true = 0 := by
    -- The junk value is read through the definitions: `labelRank` is `leastLevel`, an `sInf`
    -- of the empty set of stages fixing `true`.
    simp [StageProjection.labelRank, leastLevel, constFalse]
  refine ⟨h, fun hiff ↦ ?_⟩
  exact Bool.false_ne_true (hiff.mp h.le)

/-! ### (W1) Quantifier order: uniformity across presentations -/

/-- Theorem 2 with the eventual-agreement premise in the **swapped order** `∀ c ∀ β ℓ ∃ α_c ℓ_c`,
as a closed statement, even under global eventual fixation. -/
def SwappedOrderStatement : Prop :=
  ∀ (I : Type u) (C : Type v) [Countable C] (S : CountablyFixedProjection I)
    (Adm : Ordinal.{0} → (C → I) → Prop),
    (∀ α, α < Ordinal.omega 1 → ∀ ℓ, Adm α ℓ → S.FixedAt α ℓ) →
    (∀ c, ∀ β ℓ, ∃ α_c < Ordinal.omega 1, ∃ ℓ_c, Adm α_c ℓ_c ∧
      (α_c < β → β < Ordinal.omega 1 → Adm β ℓ → ℓ c = ℓ_c c)) →
    ∃ A < Ordinal.omega 1, ∀ β, β < Ordinal.omega 1 → ∀ ℓ, Adm β ℓ → S.FixedAt A ℓ

/-- The ladder: at countable stage `β` the single coordinate carries the label `β`. -/
def ladderAdm (β : Ordinal.{0}) (ℓ : Unit → CO) : Prop := (ℓ ()).1 = β

theorem ladderAdm_stage : ∀ α, α < Ordinal.omega 1 → ∀ ℓ, ladderAdm α ℓ → P.FixedAt α ℓ := by
  rintro α - ℓ h ⟨⟩
  exact P_fixed_iff.mpr h.le

theorem ladderAdm_swapped : ∀ c : Unit, ∀ β ℓ, ∃ α_c < Ordinal.omega 1, ∃ ℓ_c,
    ladderAdm α_c ℓ_c ∧ (α_c < β → β < Ordinal.omega 1 → ladderAdm β ℓ → ℓ c = ℓ_c c) := by
  intro _ β _
  by_cases hβ : β < Ordinal.omega 1
  · exact ⟨β, hβ, fun _ ↦ ⟨β, hβ⟩, rfl, fun h ↦ absurd h (lt_irrefl β)⟩
  · exact ⟨0, Ordinal.omega_pos 1, fun _ ↦ ⟨0, Ordinal.omega_pos 1⟩, rfl,
      fun _ h ↦ absurd h hβ⟩

theorem ladder_no_uniform : ¬ ∃ A < Ordinal.omega 1, ∀ β, β < Ordinal.omega 1 → ∀ ℓ,
    ladderAdm β ℓ → P.FixedAt A ℓ := by
  rintro ⟨A, hA, h⟩
  have hA1 := succ_lt_omega1 hA
  exact P_not_fixed_succ A hA1 (h (A + 1) hA1 (fun _ ↦ ⟨A + 1, hA1⟩) rfl ())

theorem not_swappedOrderStatement : ¬ SwappedOrderStatement.{1, 0} := fun h ↦
  ladder_no_uniform (h CO Unit P ladderAdm ladderAdm_stage ladderAdm_swapped)

/-- The ladder violates the real (unswapped) premise. -/
theorem ladder_not_ev : ¬ ∀ c, EventuallyInvariant ladderAdm c := fun h ↦
  ladder_no_uniform (P.exists_uniform_fixing_stage ladderAdm ladderAdm_stage h)

/-! ### (W2) The witness pins the explicit bound, not existence -/

/-- Only the label `2`, only at stages `≥ 2`. -/
def twoAdm (β : Ordinal.{0}) (ℓ : Unit → CO) : Prop :=
  ((2 : ℕ) : Ordinal.{0}) ≤ β ∧ (ℓ ()).1 = (2 : ℕ)

theorem twoAdm_stage : ∀ α, α < Ordinal.omega 1 → ∀ ℓ, twoAdm α ℓ → P.FixedAt α ℓ := by
  rintro α - ℓ ⟨h2, h⟩ ⟨⟩
  exact P_fixed_iff.mpr (h ▸ h2)

/-- The eventual value `2` after threshold `0`. -/
def two : CO := natLabel 2

theorem twoAdm_const : ∀ c : Unit, ∀ β, (0 : Ordinal.{0}) < β → β < Ordinal.omega 1 →
    ∀ ℓ, twoAdm β ℓ → ℓ c = two :=
  fun _ _ _ _ _ h ↦ Subtype.ext h.2

theorem twoAdm_no_zero_witness : ∀ ℓ, ¬ twoAdm 0 ℓ := by
  rintro _ ⟨h, -⟩
  rw [← Nat.cast_zero, Nat.cast_le] at h
  exact absurd h (by decide)

/-- Existence survives with a bare value, both without and with an explicit stage. -/
theorem two_uniform :
    (∃ A < Ordinal.omega 1, ∀ β, β < Ordinal.omega 1 → ∀ ℓ, twoAdm β ℓ → P.FixedAt A ℓ) ∧
      ((⨆ _ : Unit, max (0 : Ordinal.{0}) (P.labelRank two)) < Ordinal.omega 1 ∧
        ∀ β, β < Ordinal.omega 1 → ∀ ℓ, twoAdm β ℓ →
          P.FixedAt (⨆ _ : Unit, max (0 : Ordinal.{0}) (P.labelRank two)) ℓ) ∧
      ∀ β, β < Ordinal.omega 1 → ∀ ℓ, twoAdm β ℓ →
        P.FixedAt (⨆ _ : Unit, max (0 : Ordinal.{0}) (P.labelRank two)) ℓ :=
  ⟨P.exists_uniform_fixing_stage_of_eventually_const twoAdm twoAdm_stage
      fun c ↦ ⟨0, Ordinal.omega_pos 1, two, twoAdm_const c⟩,
    P.uniform_fixing_of_eventual_values twoAdm twoAdm_stage (fun _ ↦ 0)
      (fun _ ↦ Ordinal.omega_pos 1) (fun _ ↦ two) twoAdm_const,
    P.toStageProjection.uniform_fixing_of_eventual_values twoAdm twoAdm_stage (fun _ ↦ 0)
      (fun _ ↦ two) (fun _ ↦ ⟨_, P.fixed_labelRank two⟩) twoAdm_const⟩

/-- The explicit stage there is `2`. -/
theorem two_explicit_stage :
    (⨆ _ : Unit, max (0 : Ordinal.{0}) (P.labelRank two)) = ((2 : ℕ) : Ordinal.{0}) := by
  rw [ciSup_const, P_labelRank, max_eq_right zero_le]
  rfl

/-- With the bare value at threshold `0`, the formula `⨆ c, (α_c + 1) = 1` is NOT uniform. -/
theorem bare_value_explicit_bound_fails :
    ¬ ∀ β, β < Ordinal.omega 1 → ∀ ℓ, twoAdm β ℓ →
      P.FixedAt (⨆ _ : Unit, ((0 : Ordinal.{0}) + 1)) ℓ := by
  intro h
  have := P_fixed_iff.mp (h _ (natCast_lt_omega1 2) (fun _ ↦ two) ⟨le_rfl, rfl⟩ ())
  rw [ciSup_const, zero_add] at this
  have h2 : ((2 : ℕ) : Ordinal.{0}) ≤ ((1 : ℕ) : Ordinal.{0}) := by rw [Nat.cast_one]; exact this
  exact absurd (Nat.cast_le.mp h2) (by decide)

/-- With the actual witness (stage `2`), Theorem 2 applies and its explicit stage is `3`. -/
theorem two_ev : ∀ c, EventuallyInvariant twoAdm c :=
  fun _ ↦ ⟨(2 : ℕ), natCast_lt_omega1 2, fun _ ↦ two, ⟨le_rfl, rfl⟩,
    fun _ _ _ _ h ↦ Subtype.ext h.2⟩

theorem two_witnessed : ∃ A < Ordinal.omega 1, ∀ β, β < Ordinal.omega 1 → ∀ ℓ, twoAdm β ℓ →
    P.FixedAt A ℓ :=
  P.exists_uniform_fixing_stage twoAdm twoAdm_stage two_ev

end UniformFixationGuard

/-! ### Import closure and axiom audit -/

/-- The modules transitively imported by `m` (including `m`), read from the environment
header. -/
partial def importClosure (env : Environment) (m : Name) : NameSet :=
  go [m] {}
where
  go : List Name → NameSet → NameSet
    | [], seen => seen
    | m :: rest, seen =>
      if seen.contains m then go rest seen
      else
        let deps := match env.getModuleIdx? m with
          | some idx => (env.header.moduleData[idx.toNat]!).imports.toList.map (·.module)
          | none => []
        go (deps ++ rest) (seen.insert m)

/-- Module-name prefixes no module of the closure may have. -/
def forbiddenPrefixes : List Name :=
  [`InfinitaryLogic.Scott, `InfinitaryLogic.ScottProcess, `InfinitaryLogic.Descriptive,
   `InfinitaryLogic.ModelTheory, `InfinitaryLogic.Karp, `InfinitaryLogic.Lomega1omega]

/-- The exact `InfinitaryLogic` import closure of the module.  Extending it is a deliberate
decision: update this list together with the module docstring. -/
def allowedClosure : List Name :=
  [`InfinitaryLogic.UniformFixation, `InfinitaryLogic.OrdinalCountability,
   `InfinitaryLogic.OrdinalUtil]

/-- The public declarations of the module that must be present. -/
def moduleDecls : List Name :=
  [`StageProjection, `StageProjection.project_project, `CountablyFixedProjection,
   `StageProjection.fixed_mono, `StageProjection.FixedAt, `StageProjection.FixedAt.mono,
   `StageProjection.exists_fixing_stage_of_forall, `StageProjection.labelRank,
   `StageProjection.labelRank_le_of_fixed, `StageProjection.fixed_labelRank_of_exists,
   `StageProjection.labelRank_le_iff_of_exists, `StageProjection.iUnion_fixedLabels_eq_univ_iff,
   `StageProjection.forall_fixed_iff_iSup_labelRank_le_of_exists,
   `StageProjection.EventuallyInvariant,
   `StageProjection.uniform_fixing_at_iSup_add_one_of_witnesses,
   `StageProjection.uniform_fixing_at_iSup_of_witnesses,
   `StageProjection.uniform_fixing_of_eventual_values,
   `StageProjection.exists_uniform_fixing_stage,
   `StageProjection.exists_uniform_fixing_stage_of_eventually_const,
   `StageProjection.labelRank_le_stage_of_adm, `StageProjection.labelRank_le_of_adm,
   `StageProjection.uniform_fixed_iff_labelRank_le,
   `StageProjection.exists_classwise_labelRank_bound,
   `CountablyFixedProjection.iUnion_fixedLabels_eq_univ,
   `CountablyFixedProjection.fixed_labelRank, `CountablyFixedProjection.labelRank_lt_omega1,
   `CountablyFixedProjection.labelRank_le_iff, `CountablyFixedProjection.exists_labelRank_gt_iff,
   `CountablyFixedProjection.exists_fixing_stage_of_countable,
   `CountablyFixedProjection.iSup_labelRank_lt_omega1,
   `CountablyFixedProjection.forall_fixed_iff_iSup_labelRank_le,
   `CountablyFixedProjection.uniform_fixing_of_eventual_values].map (`InfinitaryLogic ++ ·)

/-- The guard's own declarations whose axioms are audited. -/
def guardDecls : List Name :=
  [`P, `P_fixed_iff, `P_labelRank, `P_labelRank_api, `simp_law, `P_rank_gt, `empty_fixed,
   `empty_explicit_bound,
   `empty_explicit, `empty_uniform, `empty_least, `natAdm_ev, `natPres_injective,
   `natAdm_no_infinite_stage, `nat_uniform, `nat_uniform_iff, `nat_explicit_bound,
   `nat_explicit, `nat_labelRank, `nat_classwise_iff, `nat_classwise, `nat_least_fixing_stage,
   `presentation_rank_rfl, `nat_least_law_only, `nat_theorem1, `nat_shared, `coAdm_ev,
   `co_no_uniform, `co_not_countable,
   `co_no_fixing_stage, `co_no_classwise_bound, `zeroAdm_ev, `zeroAdm_not_stage,
   `zeroAdm_no_uniform, `uniform_of_unguarded, `eventuallyInvariant_iff, `junk_labelRank,
   `not_swappedOrderStatement, `ladder_not_ev, `twoAdm_no_zero_witness, `two_uniform,
   `two_explicit_stage, `bare_value_explicit_bound_fails, `two_ev, `two_witnessed].map
    (`UniformFixationGuard ++ ·)

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

-- The closure check and the axiom audit run in one command, so that the final OK line is
-- printed only when both pass.
run_cmd do
  let env ← getEnv
  let target := `InfinitaryLogic.UniformFixation
  let some idx := env.getModuleIdx? target
    | throwError "module {target} is not in the environment"
  let cl := importClosure env target
  let ilModules := cl.toList.filter fun m ↦ (`InfinitaryLogic).isPrefixOf m
  let hits := ilModules.filter fun m ↦ forbiddenPrefixes.any (·.isPrefixOf m)
  unless hits.isEmpty do
    throwError "[BROAD CONE] the closure of {target} reaches {hits}"
  let extra := ilModules.filter fun m ↦ !allowedClosure.contains m
  let missing := allowedClosure.filter fun m ↦ !ilModules.contains m
  unless extra.isEmpty && missing.isEmpty do
    throwError "[CLOSURE DRIFT] the InfinitaryLogic closure of {target} is {ilModules}; \
      update allowedClosure deliberately (extra {extra}, missing {missing})"
  let enumerated := (env.header.moduleData[idx.toNat]!).constNames.toList
  for n in moduleDecls do
    unless enumerated.contains n do throwError "declaration {n} not found in the module"
  for n in enumerated ++ guardDecls do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo m!"Uniform fixation regression guard: OK (applied: the simp law, rank/fixedness \
    duality, law-only leastness of the label-rank supremum; empty coordinates with bound 0; \
    C = N with per-coordinate witnesses at different stages, uniform stages exactly >= omega, \
    explicit stage omega in both forms, realized label ranks min m n, classwise bound iff \
    omega <= A, least fixing stage omega; uncountable C = Iio omega_1 negative for the uniform \
    stage, Theorem 1 and the classwise bound; stage correctness dropped gives no uniform stage; \
    one stage for presentations at different stages; the contract premise forms; the junk \
    label rank; swapped quantifier order refuted (uniformity across presentations); bare \
    value: existence survives, also at the explicit eventual-value stage (countable when \
    bundled), the explicit formula fails (the witness pins the explicit bound); import \
    closure exactly {allowedClosure}; standard axioms on \
    {enumerated.length} module declarations and {guardDecls.length} guard declarations)"
