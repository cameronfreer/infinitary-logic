/-
Client-adapter acceptance guard for `InfinitaryLogic/UniformFixation.lean`.

A downstream consumer bounds, class by class, the label rank of every label occurring in an
admissible presentation.  Classes are indexed by `q : Q`, each with its own countable coordinate
type `C q` and its own admissible presentations `Adm q`; a projection system carrying global
eventual fixation is fixed once.  The consumer applies uniform fixation to one class and reads
off label ranks through `labelRank_le_iff`.  This guard states that consumer, in this library's
vocabulary, against the exports alone, with the three-line proof it uses (uniform fixation,
unpack an occurrence, `labelRank_le_iff`), and checks:

* **`classwise_labelRank_bound`**: the consumer theorem, proved by `exists_uniform_fixing_stage`
  then `labelRank_le_iff`, through dot notation on a `CountablyFixedProjection`;
* **`classwise_labelRank_bound_of_stageProjection`**: the same bound needs no eventual fixation
  (law-only `StageProjection`, through `labelRank_le_of_adm`);
* **the consumer's shapes are instances of the exports**: a bundled projection with the law and
  eventual fixation at countable stages is a `CountablyFixedProjection`; the
  eventual-invariance premise (witness at the threshold, strict `α < β`, guard `β < ω₁`) is
  `EventuallyInvariant` by `Iff.rfl`; the uniform-fixation shape (guarded stage correctness,
  conclusion `∃ A < ω₁, ∀ β, β < ω₁ → ∀ ℓ, Adm β ℓ → S.FixedAt A ℓ`) is
  `exists_uniform_fixing_stage` by `exact`; the rank shape is `labelRank_le_iff`;
* **`ω₁` spelled `(aleph 1).ord`**: the same shapes with that spelling, through the single
  rewrite `Cardinal.ord_aleph` (the documented variant; the library spells `ω₁` as
  `Ordinal.omega 1`).

Nothing downstream is modified; this file is the scratch client.  All declarations of this
guard use only the standard axioms.

Run with: lake env lean scripts/check_uniform_fixation_client.lean
-/
import InfinitaryLogic.UniformFixation

open Lean InfinitaryLogic

universe u v w

namespace UniformFixationClient

variable {Q : Type u} {I : Type v} {C : Q → Type w}

/-- The label `i` occurs in some admissible presentation of class `q` at a countable stage. -/
def Occurs (Adm : ∀ q, Ordinal.{0} → (C q → I) → Prop) (q : Q) (i : I) : Prop :=
  ∃ β < Ordinal.omega 1, ∃ ℓ, Adm q β ℓ ∧ ∃ c, ℓ c = i

/-- **The consumer.**  Class by class, one countable stage bounds the label rank of every label
occurring in an admissible presentation of that class. -/
theorem classwise_labelRank_bound [∀ q, Countable (C q)] (S : CountablyFixedProjection I)
    (Adm : ∀ q, Ordinal.{0} → (C q → I) → Prop)
    (hstage : ∀ q α, α < Ordinal.omega 1 → ∀ ℓ, Adm q α ℓ → S.FixedAt α ℓ)
    (hev : ∀ q c, StageProjection.EventuallyInvariant (Adm q) c) :
    ∀ q, ∃ A < Ordinal.omega 1, ∀ i, Occurs Adm q i → S.labelRank i ≤ A := by
  intro q
  obtain ⟨A, hA, h⟩ := S.exists_uniform_fixing_stage (Adm q) (hstage q) (hev q)
  refine ⟨A, hA, fun i hi => ?_⟩
  obtain ⟨β, hβ, ℓ, hℓ, c, rfl⟩ := hi
  exact S.labelRank_le_iff.mpr (h β hβ ℓ hℓ c)

/-- The same bound for a law-only projection system: eventual fixation is not used. -/
theorem classwise_labelRank_bound_of_stageProjection [∀ q, Countable (C q)]
    (S : StageProjection I) (Adm : ∀ q, Ordinal.{0} → (C q → I) → Prop)
    (hstage : ∀ q α, α < Ordinal.omega 1 → ∀ ℓ, Adm q α ℓ → S.FixedAt α ℓ)
    (hev : ∀ q c, StageProjection.EventuallyInvariant (Adm q) c) :
    ∀ q, ∃ A < Ordinal.omega 1, ∀ i, Occurs Adm q i → S.labelRank i ≤ A := by
  intro q
  obtain ⟨A, hA, h⟩ := S.exists_uniform_fixing_stage (Adm q) (hstage q) (hev q)
  refine ⟨A, hA, fun i hi => ?_⟩
  obtain ⟨β, hβ, ℓ, hℓ, c, rfl⟩ := hi
  exact StageProjection.labelRank_le_of_adm h hβ hℓ c

/-! ### The consumer's shapes are instances of the exports -/

/-- A bundled projection: the law and eventual fixation at countable stages. -/
def ofBundle (project : Ordinal.{0} → I → I)
    (law : ∀ α β i, project α (project β i) = project (min α β) i)
    (fixed : ∀ i, ∃ α < Ordinal.omega 1, project α i = i) : CountablyFixedProjection I :=
  { project, project_project := law, eventually_fixed := fixed }

/-- The eventual-invariance shape is `EventuallyInvariant`, definitionally. -/
theorem eventuallyInvariant_shape {D : Type w} (Adm : Ordinal.{0} → (D → I) → Prop) (c : D) :
    (∃ α < Ordinal.omega 1, ∃ ℓ : D → I, Adm α ℓ ∧
      ∀ β, α < β → β < Ordinal.omega 1 → ∀ ℓ', Adm β ℓ' → ℓ' c = ℓ c) ↔
      StageProjection.EventuallyInvariant Adm c :=
  Iff.rfl

/-- The uniform-fixation shape is `exists_uniform_fixing_stage`, by `exact`. -/
theorem uniform_shape {D : Type w} [Countable D] (S : CountablyFixedProjection I)
    (Adm : Ordinal.{0} → (D → I) → Prop)
    (hstage : ∀ α, α < Ordinal.omega 1 → ∀ ℓ, Adm α ℓ → S.FixedAt α ℓ)
    (hev : ∀ c, StageProjection.EventuallyInvariant Adm c) :
    ∃ A < Ordinal.omega 1, ∀ β, β < Ordinal.omega 1 → ∀ ℓ, Adm β ℓ → S.FixedAt A ℓ := by
  exact S.exists_uniform_fixing_stage Adm hstage hev

/-- The fixed-at shape unfolds to pointwise fixation. -/
theorem fixedAt_shape {D : Type w} (S : CountablyFixedProjection I) (α : Ordinal.{0})
    (ℓ : D → I) : S.FixedAt α ℓ ↔ ∀ c, S.project α (ℓ c) = ℓ c :=
  Iff.rfl

/-- The rank shape. -/
theorem rank_shape (S : CountablyFixedProjection I) {i : I} {α : Ordinal.{0}} :
    S.labelRank i ≤ α ↔ S.project α i = i :=
  S.labelRank_le_iff

/-! ### The same shapes with `ω₁` spelled `(aleph 1).ord` -/

/-- A bundle with eventual fixation below `(aleph 1).ord`. -/
def ofBundleAleph (project : Ordinal.{0} → I → I)
    (law : ∀ α β i, project α (project β i) = project (min α β) i)
    (fixed : ∀ i, ∃ α < (Cardinal.aleph 1).ord, project α i = i) : CountablyFixedProjection I :=
  ofBundle project law (by simpa only [Cardinal.ord_aleph] using fixed)

theorem eventuallyInvariant_shape_aleph {D : Type w} (Adm : Ordinal.{0} → (D → I) → Prop)
    (c : D) :
    (∃ α < (Cardinal.aleph 1).ord, ∃ ℓ : D → I, Adm α ℓ ∧
      ∀ β, α < β → β < (Cardinal.aleph 1).ord → ∀ ℓ', Adm β ℓ' → ℓ' c = ℓ c) ↔
      StageProjection.EventuallyInvariant Adm c := by
  rw [Cardinal.ord_aleph]
  exact Iff.rfl

theorem uniform_shape_aleph {D : Type w} [Countable D] (S : CountablyFixedProjection I)
    (Adm : Ordinal.{0} → (D → I) → Prop)
    (hstage : ∀ α, α < (Cardinal.aleph 1).ord → ∀ ℓ, Adm α ℓ → S.FixedAt α ℓ)
    (hev : ∀ c, ∃ α < (Cardinal.aleph 1).ord, ∃ ℓ : D → I, Adm α ℓ ∧
      ∀ β, α < β → β < (Cardinal.aleph 1).ord → ∀ ℓ', Adm β ℓ' → ℓ' c = ℓ c) :
    ∃ A < (Cardinal.aleph 1).ord, ∀ β, β < (Cardinal.aleph 1).ord → ∀ ℓ, Adm β ℓ →
      S.FixedAt A ℓ := by
  rw [Cardinal.ord_aleph] at hstage hev ⊢
  exact S.exists_uniform_fixing_stage Adm hstage hev

end UniformFixationClient

/-! ### Axiom audit -/

/-- The guard's declarations whose axioms are audited. -/
def clientDecls : List Name :=
  [`Occurs, `classwise_labelRank_bound, `classwise_labelRank_bound_of_stageProjection,
   `ofBundle, `eventuallyInvariant_shape, `uniform_shape, `fixedAt_shape, `rank_shape,
   `ofBundleAleph, `eventuallyInvariant_shape_aleph, `uniform_shape_aleph].map
    (`UniformFixationClient ++ ·)

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in clientDecls do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "Uniform fixation client guard: OK (the classwise label-rank consumer compiles against \
    the exports with its three-line proof, also for a law-only projection system; the bundled \
    projection, eventual-invariance, uniform-fixation, fixed-at and rank shapes are instances \
    of the exports, with omega_1 spelled Ordinal.omega 1 and, through Cardinal.ord_aleph, \
    (aleph 1).ord; standard axioms)"
