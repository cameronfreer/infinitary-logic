/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.OrdinalCountability

/-!
# Uniform fixation of labels under stage projections

A single label type `I` carries projections `project α : I → I` indexed by stages
`α : Ordinal.{0}`, subject to the projection law
`project α (project β i) = project (min α β) i` (`StageProjection`).  A label `i` is *fixed at*
`α` when `project α i = i`, and a presentation `ℓ : C → I` is fixed at `α`
(`StageProjection.FixedAt`) when every coordinate is.  `CountablyFixedProjection` adds that every
label is fixed at some countable stage.  No logic is involved; `ω₁` is `Ordinal.omega 1`.

## Main results

* `StageProjection.fixed_mono`: fixedness is upward closed (the projection law alone).
* **Theorem 1** (one presentation).  `StageProjection.exists_fixing_stage_of_forall`: if each
  coordinate of a countable presentation is fixed at some countable stage, all are fixed at one
  countable stage; `CountablyFixedProjection.exists_fixing_stage_of_countable` is the instance
  under global eventual fixation.  The bound depends on `ℓ`.  The countable supremum is Mathlib's
  `Ordinal.iSup_lt_omega_one`, which takes an arbitrary countable index type, empty included; the
  `ℕ`-indexed `iSup_lt_omega1_of_forall_lt` would need an enumeration and an empty-case split.
* **The label rank.**  `StageProjection.labelRank S i` is the least stage fixing `i`, defined
  through `leastLevel` of the family `α ↦ {i | project α i = i}`.  Without an existence premise it
  means nothing (junk value `0` for a label fixed at no stage), so every lemma beyond
  `labelRank_le_of_fixed` assumes one: `fixed_labelRank_of_exists` and
  `labelRank_le_iff_of_exists` for one label; `iUnion_fixedLabels_eq_univ_iff` identifies the
  covering hypothesis of `leastLevel` with global eventual fixation, under which
  (`CountablyFixedProjection`) `fixed_labelRank`, `labelRank_lt_omega1` and `labelRank_le_iff`
  hold with no further premise.  The least simultaneous fixing stage of one countable
  presentation is `⨆ c, labelRank (ℓ c)` (`forall_fixed_iff_iSup_labelRank_le`).  The fixing rank
  of coordinate `c` in a presentation `ℓ`, the least level of `α ↦ {c | project α (ℓ c) = ℓ c}`,
  is *definitionally* `labelRank (ℓ c)`, so no separate presentation rank is defined.
* **Theorem 2** (uniform fixation; `StageProjection.exists_uniform_fixing_stage`).  Let
  `Adm : Ordinal.{0} → (C → I) → Prop` single out the admissible presentations at each stage, `C`
  countable.  Assume *stage correctness* (an admissible presentation at a countable stage `β` is
  fixed at `β`) and, for every coordinate, `EventuallyInvariant Adm c`: some admissible witness
  presentation `ℓ_c` at a countable stage `α_c` such that every admissible presentation at every
  countable stage `β > α_c` agrees with `ℓ_c` at `c` (quantifier order `∀ c ∃ α_c ℓ_c ∀ β ℓ`; the
  witnesses are per coordinate, and no single presentation need contain them all).  Then one
  countable stage `A` fixes every coordinate of every admissible presentation at every countable
  stage.  Explicitly `A = ⨆ c, (α_c + 1)` (`uniform_fixing_of_witnesses`): at `β ≤ A` stage
  correctness and monotonicity apply; at `β > A` the label is the witness value, which is fixed
  at `α_c < A` by stage correctness *of the witness*.  `⨆ c, α_c` also works
  (`uniform_fixing_at_iSup_of_witnesses`).  No admissible presentation is assumed to exist at
  any high stage, and empty `C` gives `A = 0`.
* **Classwise label-rank bounds.**  `labelRank_le_stage_of_adm`, `labelRank_le_of_adm`,
  `uniform_fixed_iff_labelRank_le` and `exists_classwise_labelRank_bound`: one countable `A`
  bounds the label rank of every coordinate of every admissible presentation.  None of these
  needs global eventual fixation; stage correctness supplies the existence premise for every
  realized label.

## What the admissible witness does

The witness `ℓ_c` at stage `α_c` justifies fixation of the eventual value at the threshold
`α_c`, and hence the *advertised* explicit bound `⨆ c, (α_c + 1)`, a term in the thresholds
alone.  It is not indispensable for every existential formulation: with global eventual
fixation of every label, merely supplying an eventual value `v_c` per coordinate still yields
*some* uniform stage, by including the values' fixing stages in the supremum
(`CountablyFixedProjection.uniform_fixing_of_eventual_values`, stage
`⨆ c, max α_c (labelRank v_c)`); `exists_uniform_fixing_stage_of_eventually_const` gives that
existence even without global eventual fixation.  With a bare value the formula
`⨆ c, (α_c + 1)` itself can fail.  Separately, the *quantifier
order* is what makes the stage uniform across presentations: with `∀ c ∀ β ℓ ∃ α_c ℓ_c` the
premise holds trivially and no uniform stage need exist; that counterexample tests uniformity
across presentations and does not by itself show that the admissible witness is needed.  These
are two different tests and the regression guard keeps them apart.

## Relation to the reference shapes

The exports are shaped so that a client stated for a bundled projection carrying eventual
fixation is instantiated with no glue: `CountablyFixedProjection` bundles `project`, the law
`project_project` and `eventually_fixed`; `FixedAt`, `EventuallyInvariant`, the stage-correctness
premise `∀ α, α < ω₁ → ∀ ℓ, Adm α ℓ → S.FixedAt α ℓ` and the conclusion
`∃ A < ω₁, ∀ β, β < ω₁ → ∀ ℓ, Adm β ℓ → S.FixedAt A ℓ` are stated with exactly that binder
structure, and `labelRank_le_iff` has the shape `S.labelRank i ≤ α ↔ S.project α i = i`.  The
deliberate differences:

* stage correctness is assumed only at countable stages (`α < ω₁ →`).  An unguarded premise
  `∀ β ℓ, Adm β ℓ → ∀ c, project β (ℓ c) = ℓ c` is the special case `fun β _ ℓ h ↦ hcorrect β ℓ h`;
* `ω₁` is spelled `Ordinal.omega 1`; `Cardinal.ord_aleph` rewrites `(aleph 1).ord` to it;
* Theorem 2 and the classwise bounds live on `StageProjection` (the law alone), so they apply to a
  `CountablyFixedProjection` through its parent, and need no eventual fixation;
* the eventual-agreement premise of `EventuallyInvariant` is exactly the specified one: strict
  `α_c < β`, the guard `β < ω₁`, and the witness at the threshold `α_c` itself;
* no least fixing stage of a whole presentation is defined: it is `⨆ c, labelRank (ℓ c)`.

## Relation to the retraction-preservation reading

An earlier reading assumed, coordinate by coordinate, that from some stage on retracting an
admissible presentation preserves the coordinate (invariance as a hypothesis), and concluded
simultaneous preservation from a countable supremum.  Here invariance is *derived*: stage
correctness plus eventual agreement with an admissible witness yield the uniform stage.  Neither
statement is an instance of the other without an adapter (pointwise projection is a coherent
retraction only on stage-correct presentations), and nothing here is stated in terms of
retractions.

## Non-claims

* No admissible presentation is shown to exist at any (high) stage.
* No maximality or leastness of the uniform stage `A` of Theorem 2; leastness is proved only for
  the simultaneous fixing stage of one presentation (`forall_fixed_iff_iSup_labelRank_le`).
* No identification of `labelRank` with any model-theoretic rank (Scott rank included).
* `labelRank` has no meaning without an existence or covering premise (junk value `0`).
* Nothing for uncountable `C`: Theorems 1 and 2 and the classwise bound fail for `C = Iio ω₁`.
* Nothing about stages `≥ ω₁`: the premises and conclusions quantify over countable stages.
* Empty `C` is allowed; the explicit bound is then `0`.
-/

universe u v

open Set

namespace InfinitaryLogic

/-- **Countable supremum of successors.**  Countably many countable ordinals have a countable
supremum of successors (`ω₁` is a successor limit). -/
theorem iSup_add_one_lt_omega1 {C : Type v} [Countable C] (α : C → Ordinal.{0})
    (hα : ∀ c, α c < Ordinal.omega 1) : (⨆ c, (α c + 1)) < Ordinal.omega 1 :=
  Ordinal.iSup_lt_omega_one fun c ↦ (Cardinal.isSuccLimit_omega 1).add_one_lt (hα c)

/-- **Stage projections** on a label type `I`: `project α` for every stage `α : Ordinal.{0}`,
with the projection law `project α (project β i) = project (min α β) i`.  No eventual fixation
is assumed (see `CountablyFixedProjection`). -/
structure StageProjection (I : Type u) where
  /-- Projection to stage `α`. -/
  project : Ordinal.{0} → I → I
  /-- The projection law. -/
  project_project : ∀ α β i, project α (project β i) = project (min α β) i

/-- Stage projections under which every label is fixed at some countable stage. -/
structure CountablyFixedProjection (I : Type u) extends StageProjection I where
  /-- Every label is fixed at a countable stage. -/
  eventually_fixed : ∀ i, ∃ α < Ordinal.omega 1, project α i = i

namespace StageProjection

variable {I : Type u} {C : Type v} (S : StageProjection I)

/-! ### Fixedness -/

/-- **Fixedness is upward closed**; only the projection law is used. -/
theorem fixed_mono {α β : Ordinal.{0}} (h : α ≤ β) {i : I} (hi : S.project α i = i) :
    S.project β i = i :=
  calc S.project β i = S.project β (S.project α i) := by rw [hi]
    _ = S.project α i := by rw [S.project_project, min_eq_right h]
    _ = i := hi

/-- A presentation `ℓ : C → I` is **fixed at** `α` when every coordinate is. -/
def FixedAt (α : Ordinal.{0}) (ℓ : C → I) : Prop :=
  ∀ c, S.project α (ℓ c) = ℓ c

variable {S}

theorem FixedAt.mono {α β : Ordinal.{0}} {ℓ : C → I} (h : S.FixedAt α ℓ) (hαβ : α ≤ β) :
    S.FixedAt β ℓ :=
  fun c ↦ S.fixed_mono hαβ (h c)

variable (S)

/-! ### Theorem 1: one presentation -/

/-- **Theorem 1, per coordinate.**  If each coordinate of a countable presentation is fixed at
some countable stage, all coordinates are fixed at one countable stage (the supremum). -/
theorem exists_fixing_stage_of_forall [Countable C] (ℓ : C → I)
    (hfix : ∀ c, ∃ α < Ordinal.omega 1, S.project α (ℓ c) = ℓ c) :
    ∃ A < Ordinal.omega 1, S.FixedAt A ℓ := by
  choose σ hσ hσfix using hfix
  exact ⟨⨆ c, σ c, Ordinal.iSup_lt_omega_one hσ,
    fun c ↦ S.fixed_mono (Ordinal.le_iSup σ c) (hσfix c)⟩

/-! ### The label rank, through `leastLevel` -/

/-- The **label rank** of `i`: the least stage fixing `i`, as the least level of the family
`α ↦ {i | project α i = i}`.  Junk value `0` for a label fixed at no stage, so the lemmas below
assume an existence premise (or, on `CountablyFixedProjection`, global eventual fixation).  For
a presentation `ℓ`, the least level of `α ↦ {c | project α (ℓ c) = ℓ c}` at `c` is
`labelRank (ℓ c)` by `rfl`. -/
noncomputable def labelRank (i : I) : Ordinal.{0} :=
  leastLevel (fun α ↦ {i : I | S.project α i = i}) i

variable {S}

/-- The label rank is at most every stage fixing the label (no premise). -/
theorem labelRank_le_of_fixed {i : I} {α : Ordinal.{0}} (h : S.project α i = i) :
    S.labelRank i ≤ α :=
  leastLevel_le_of_mem (Q := fun α ↦ {i : I | S.project α i = i}) h

/-- A label fixed at some stage is fixed at its label rank. -/
theorem fixed_labelRank_of_exists {i : I} (h : ∃ α, S.project α i = i) :
    S.project (S.labelRank i) i = i :=
  leastLevel_mem_of_exists (Q := fun α ↦ {i : I | S.project α i = i}) h

/-- `labelRank_le_iff` under the existence premise for the one label `i`. -/
theorem labelRank_le_iff_of_exists {i : I} (h : ∃ α, S.project α i = i) {α : Ordinal.{0}} :
    S.labelRank i ≤ α ↔ S.project α i = i :=
  ⟨fun hle ↦ S.fixed_mono hle (fixed_labelRank_of_exists h), labelRank_le_of_fixed⟩

variable (S) in
/-- The covering hypothesis of `leastLevel` for the label family is global eventual fixation. -/
theorem iUnion_fixedLabels_eq_univ_iff :
    (⋃ α < Ordinal.omega 1, {i : I | S.project α i = i}) = Set.univ ↔
      ∀ i, ∃ α < Ordinal.omega 1, S.project α i = i := by
  simp only [Set.eq_univ_iff_forall, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]

/-! ### Theorem 2: uniform fixation -/

/-- A coordinate `c` is **eventually invariant** across the admissible presentations: there is
an admissible witness presentation `ℓ` at a countable stage `α` such that every admissible
presentation at every countable stage `β > α` agrees with `ℓ` at `c`.  The witness is part of
the data: by stage correctness it fixes the eventual value at the threshold `α` itself. -/
def EventuallyInvariant (Adm : Ordinal.{0} → (C → I) → Prop) (c : C) : Prop :=
  ∃ α < Ordinal.omega 1, ∃ ℓ : C → I, Adm α ℓ ∧
    ∀ β, α < β → β < Ordinal.omega 1 → ∀ ℓ', Adm β ℓ' → ℓ' c = ℓ c

variable (S)

/-- **Theorem 2, explicit stage.**  Given per-coordinate admissible witnesses `w c` at countable
stages `α c` with eventual agreement, the stage `⨆ c, (α c + 1)`, a term in `α` alone and
independent of `β` and `ℓ`, fixes every admissible presentation at every countable stage. -/
theorem uniform_fixing_of_witnesses [Countable C] (Adm : Ordinal.{0} → (C → I) → Prop)
    (hstage : ∀ α, α < Ordinal.omega 1 → ∀ ℓ, Adm α ℓ → S.FixedAt α ℓ)
    (α : C → Ordinal.{0}) (hα : ∀ c, α c < Ordinal.omega 1) (w : C → C → I)
    (hw : ∀ c, Adm (α c) (w c))
    (hagree : ∀ c, ∀ β, α c < β → β < Ordinal.omega 1 → ∀ ℓ, Adm β ℓ → ℓ c = w c c) :
    ∀ β, β < Ordinal.omega 1 → ∀ ℓ, Adm β ℓ → S.FixedAt (⨆ c, (α c + 1)) ℓ := by
  intro β hβ ℓ hℓ c
  have hαA : α c + 1 ≤ ⨆ c, (α c + 1) := Ordinal.le_iSup (fun c ↦ α c + 1) c
  rcases le_or_gt β (⨆ c, (α c + 1)) with hβA | hAβ
  · exact S.fixed_mono hβA (hstage β hβ ℓ hℓ c)
  · rw [hagree c β ((lt_add_one (α c)).trans_le (hαA.trans hAβ.le)) hβ ℓ hℓ]
    exact S.fixed_mono ((lt_add_one (α c)).le.trans hαA) (hstage _ (hα c) _ (hw c) c)

/-- **Theorem 2 at the sharper stage `⨆ c, α c`.**  Split on `β ≤ α c` rather than on
`β ≤ ⨆ c, (α c + 1)`; the successor is not needed. -/
theorem uniform_fixing_at_iSup_of_witnesses [Countable C] (Adm : Ordinal.{0} → (C → I) → Prop)
    (hstage : ∀ α, α < Ordinal.omega 1 → ∀ ℓ, Adm α ℓ → S.FixedAt α ℓ)
    (α : C → Ordinal.{0}) (hα : ∀ c, α c < Ordinal.omega 1) (w : C → C → I)
    (hw : ∀ c, Adm (α c) (w c))
    (hagree : ∀ c, ∀ β, α c < β → β < Ordinal.omega 1 → ∀ ℓ, Adm β ℓ → ℓ c = w c c) :
    ∀ β, β < Ordinal.omega 1 → ∀ ℓ, Adm β ℓ → S.FixedAt (⨆ c, α c) ℓ := by
  intro β hβ ℓ hℓ c
  rcases le_or_gt β (α c) with hβα | hαβ
  · exact S.fixed_mono (hβα.trans (Ordinal.le_iSup α c)) (hstage β hβ ℓ hℓ c)
  · rw [hagree c β hαβ hβ ℓ hℓ]
    exact S.fixed_mono (Ordinal.le_iSup α c) (hstage _ (hα c) _ (hw c) c)

/-- **Theorem 2 (uniform fixation).**  Stage correctness at countable stages and eventual
invariance of every coordinate (an admissible witness per coordinate, order `∀ c ∃ α_c ℓ_c ∀ β ℓ`)
give one countable stage fixing every admissible presentation at every countable stage.  The
stage is `⨆ c, (α_c + 1)` (`uniform_fixing_of_witnesses`), `0` for empty `C`; no admissible
presentation at any high stage is assumed to exist. -/
theorem exists_uniform_fixing_stage [Countable C] (Adm : Ordinal.{0} → (C → I) → Prop)
    (hstage : ∀ α, α < Ordinal.omega 1 → ∀ ℓ, Adm α ℓ → S.FixedAt α ℓ)
    (hev : ∀ c, EventuallyInvariant Adm c) :
    ∃ A < Ordinal.omega 1, ∀ β, β < Ordinal.omega 1 → ∀ ℓ, Adm β ℓ → S.FixedAt A ℓ := by
  choose α hα w hw hagree using hev
  exact ⟨⨆ c, (α c + 1), iSup_add_one_lt_omega1 α hα,
    S.uniform_fixing_of_witnesses Adm hstage α hα w hw hagree⟩

/-- **Existence without the admissible witness.**  The witness is not indispensable for an
existential bound: with global eventual fixation of every label, merely supplying an eventual
value `v_c` per coordinate still yields *some* uniform stage, by including the values' fixing
stages in the supremum (`CountablyFixedProjection.uniform_fixing_of_eventual_values`).  This
statement does not even assume global eventual fixation: the fixing stage used for `v_c` is the
stage of any admissible presentation above `α_c` (stage correctness fixes `v_c` there), or `α_c`
itself when there is none.  What the actual witness of `EventuallyInvariant` adds is fixation at
the threshold, hence the advertised explicit bound `⨆ c, (α_c + 1)` in the thresholds alone. -/
theorem exists_uniform_fixing_stage_of_eventually_const [Countable C]
    (Adm : Ordinal.{0} → (C → I) → Prop)
    (hstage : ∀ α, α < Ordinal.omega 1 → ∀ ℓ, Adm α ℓ → S.FixedAt α ℓ)
    (hconst : ∀ c, ∃ α < Ordinal.omega 1, ∃ v : I,
      ∀ β, α < β → β < Ordinal.omega 1 → ∀ ℓ, Adm β ℓ → ℓ c = v) :
    ∃ A < Ordinal.omega 1, ∀ β, β < Ordinal.omega 1 → ∀ ℓ, Adm β ℓ → S.FixedAt A ℓ := by
  have hcoord : ∀ c, ∃ s < Ordinal.omega 1,
      ∀ β, β < Ordinal.omega 1 → ∀ ℓ, Adm β ℓ → S.project s (ℓ c) = ℓ c := by
    intro c
    obtain ⟨α, hα, v, hv⟩ := hconst c
    by_cases hex : ∃ β₀, α < β₀ ∧ β₀ < Ordinal.omega 1 ∧ ∃ ℓ₀, Adm β₀ ℓ₀
    · obtain ⟨β₀, hαβ₀, hβ₀, ℓ₀, hℓ₀⟩ := hex
      refine ⟨β₀, hβ₀, fun β hβ ℓ hℓ ↦ ?_⟩
      rcases le_or_gt β α with hβα | hαβ
      · exact S.fixed_mono (hβα.trans hαβ₀.le) (hstage β hβ ℓ hℓ c)
      · rw [hv β hαβ hβ ℓ hℓ, ← hv β₀ hαβ₀ hβ₀ ℓ₀ hℓ₀]
        exact hstage β₀ hβ₀ ℓ₀ hℓ₀ c
    · refine ⟨α, hα, fun β hβ ℓ hℓ ↦ ?_⟩
      rcases le_or_gt β α with hβα | hαβ
      · exact S.fixed_mono hβα (hstage β hβ ℓ hℓ c)
      · exact (hex ⟨β, hαβ, hβ, ℓ, hℓ⟩).elim
  choose s hs hsfix using hcoord
  exact ⟨⨆ c, s c, Ordinal.iSup_lt_omega_one hs,
    fun β hβ ℓ hℓ c ↦ S.fixed_mono (Ordinal.le_iSup s c) (hsfix c β hβ ℓ hℓ)⟩

/-! ### Classwise label-rank bounds -/

variable {S}

/-- An admissible presentation at a countable stage `β` has label ranks at most `β`. -/
theorem labelRank_le_stage_of_adm {Adm : Ordinal.{0} → (C → I) → Prop}
    (hstage : ∀ α, α < Ordinal.omega 1 → ∀ ℓ, Adm α ℓ → S.FixedAt α ℓ) {β : Ordinal.{0}}
    (hβ : β < Ordinal.omega 1) {ℓ : C → I} (hℓ : Adm β ℓ) (c : C) : S.labelRank (ℓ c) ≤ β :=
  labelRank_le_of_fixed (hstage β hβ ℓ hℓ c)

/-- A uniform stage `A` (the conclusion of Theorem 2) bounds the label rank of every coordinate
of every admissible presentation at a countable stage (no covering premise). -/
theorem labelRank_le_of_adm {Adm : Ordinal.{0} → (C → I) → Prop} {A : Ordinal.{0}}
    (hA : ∀ β, β < Ordinal.omega 1 → ∀ ℓ, Adm β ℓ → S.FixedAt A ℓ) {β : Ordinal.{0}}
    (hβ : β < Ordinal.omega 1) {ℓ : C → I} (hℓ : Adm β ℓ) (c : C) : S.labelRank (ℓ c) ≤ A :=
  labelRank_le_of_fixed (hA β hβ ℓ hℓ c)

/-- Under stage correctness, a uniform fixing stage and a classwise label-rank bound are the same
thing (stage correctness supplies the existence premise for every realized label). -/
theorem uniform_fixed_iff_labelRank_le {Adm : Ordinal.{0} → (C → I) → Prop}
    (hstage : ∀ α, α < Ordinal.omega 1 → ∀ ℓ, Adm α ℓ → S.FixedAt α ℓ) {A : Ordinal.{0}} :
    (∀ β, β < Ordinal.omega 1 → ∀ ℓ, Adm β ℓ → S.FixedAt A ℓ) ↔
      ∀ β, β < Ordinal.omega 1 → ∀ ℓ, Adm β ℓ → ∀ c, S.labelRank (ℓ c) ≤ A :=
  ⟨fun hA _ hβ _ hℓ c ↦ labelRank_le_of_adm hA hβ hℓ c, fun h β hβ ℓ hℓ c ↦
    (labelRank_le_iff_of_exists ⟨β, hstage β hβ ℓ hℓ c⟩).mp (h β hβ ℓ hℓ c)⟩

variable (S)

/-- **Classwise bound (Theorem 2, label-rank form).**  One countable `A` bounds the label rank of
every coordinate of every admissible presentation at every countable stage. -/
theorem exists_classwise_labelRank_bound [Countable C] (Adm : Ordinal.{0} → (C → I) → Prop)
    (hstage : ∀ α, α < Ordinal.omega 1 → ∀ ℓ, Adm α ℓ → S.FixedAt α ℓ)
    (hev : ∀ c, EventuallyInvariant Adm c) :
    ∃ A < Ordinal.omega 1,
      ∀ β, β < Ordinal.omega 1 → ∀ ℓ, Adm β ℓ → ∀ c, S.labelRank (ℓ c) ≤ A :=
  let ⟨A, hA, hfix⟩ := S.exists_uniform_fixing_stage Adm hstage hev
  ⟨A, hA, fun _ hβ _ hℓ c ↦ labelRank_le_of_adm hfix hβ hℓ c⟩

end StageProjection

namespace CountablyFixedProjection

variable {I : Type u} {C : Type v} (S : CountablyFixedProjection I)

/-- The covering hypothesis of `leastLevel` for the label family. -/
theorem iUnion_fixedLabels_eq_univ :
    (⋃ α < Ordinal.omega 1, {i : I | S.project α i = i}) = Set.univ :=
  (S.iUnion_fixedLabels_eq_univ_iff).mpr S.eventually_fixed

/-- Every label is fixed at its label rank. -/
theorem fixed_labelRank (i : I) : S.project (S.labelRank i) i = i :=
  leastLevel_mem (fun α ↦ {i : I | S.project α i = i}) S.iUnion_fixedLabels_eq_univ i

/-- Label ranks are countable. -/
theorem labelRank_lt_omega1 (i : I) : S.labelRank i < Ordinal.omega 1 :=
  leastLevel_lt_omega1 (fun α ↦ {i : I | S.project α i = i}) S.iUnion_fixedLabels_eq_univ i

/-- **`labelRank_le_iff`**: the label rank is at most `α` iff `α` fixes the label. -/
theorem labelRank_le_iff {i : I} {α : Ordinal.{0}} : S.labelRank i ≤ α ↔ S.project α i = i :=
  ⟨fun h ↦ S.fixed_mono h (S.fixed_labelRank i), StageProjection.labelRank_le_of_fixed⟩

/-- **Theorem 1.**  A countable presentation has a countable fixing stage. -/
theorem exists_fixing_stage_of_countable [Countable C] (ℓ : C → I) :
    ∃ A < Ordinal.omega 1, S.FixedAt A ℓ :=
  S.exists_fixing_stage_of_forall ℓ fun c ↦ S.eventually_fixed (ℓ c)

/-- The supremum of the label ranks of a countable presentation is countable. -/
theorem iSup_labelRank_lt_omega1 [Countable C] (ℓ : C → I) :
    (⨆ c, S.labelRank (ℓ c)) < Ordinal.omega 1 :=
  Ordinal.iSup_lt_omega_one fun c ↦ S.labelRank_lt_omega1 (ℓ c)

/-- **The least simultaneous fixing stage** of a countable presentation is
`⨆ c, labelRank (ℓ c)`: a stage fixes every coordinate iff it is at least that supremum. -/
theorem forall_fixed_iff_iSup_labelRank_le [Countable C] (ℓ : C → I) {A : Ordinal.{0}} :
    (∀ c, S.project A (ℓ c) = ℓ c) ↔ (⨆ c, S.labelRank (ℓ c)) ≤ A := by
  rw [Ordinal.iSup_le_iff]
  exact forall_congr' fun c ↦ S.labelRank_le_iff.symm

/-- **Existence without the witness, explicit stage under global eventual fixation.**  With an
eventual value `v c` per coordinate after threshold `α c`, the stage
`⨆ c, max (α c) (labelRank (v c))` is uniform: the values' own fixing stages enter the supremum
in place of an admissible witness at the threshold. -/
theorem uniform_fixing_of_eventual_values [Countable C] (Adm : Ordinal.{0} → (C → I) → Prop)
    (hstage : ∀ α, α < Ordinal.omega 1 → ∀ ℓ, Adm α ℓ → S.FixedAt α ℓ)
    (α : C → Ordinal.{0}) (v : C → I)
    (hconst : ∀ c, ∀ β, α c < β → β < Ordinal.omega 1 → ∀ ℓ, Adm β ℓ → ℓ c = v c) :
    ∀ β, β < Ordinal.omega 1 → ∀ ℓ, Adm β ℓ →
      S.FixedAt (⨆ c, max (α c) (S.labelRank (v c))) ℓ := by
  intro β hβ ℓ hℓ c
  have hle := Ordinal.le_iSup (fun c ↦ max (α c) (S.labelRank (v c))) c
  rcases le_or_gt β (α c) with hβα | hαβ
  · exact S.fixed_mono (hβα.trans ((le_max_left _ _).trans hle)) (hstage β hβ ℓ hℓ c)
  · rw [hconst c β hαβ hβ ℓ hℓ]
    exact S.fixed_mono ((le_max_right _ _).trans hle) (S.fixed_labelRank (v c))

end CountablyFixedProjection

end InfinitaryLogic
