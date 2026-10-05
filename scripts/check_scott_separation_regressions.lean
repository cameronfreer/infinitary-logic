/-
Regression guard for separation by an isolating observation and the strict stage bounds
(`InfinitaryLogic/OrdinalCountability.lean`, section "Separation by an isolating observation"),
the countable quantifier rank (`BoundedFormulaω.qrank_lt_omega1` in
`InfinitaryLogic/Lomega1omega/QuantifierRank.lean`), and the wrapper on an isolated presentation
(`IsolatedPresentation.exists_countable_strict_stage_bound` in
`InfinitaryLogic/Descriptive/ScottDefinability.lean`).

Every exported declaration is *applied*, not only listed for its axioms.

* **Positive.**  A two-point class space where isolation and constant truth on the whole space
  give `False`; a domain of two other points with the isolated point outside, where the
  hypotheses hold together; a rank-zero isolating observation, with no positivity assumption,
  excluding the point from every domain; independent universes (`Type 2` classes, `Type 0`
  observations) with no `Nonempty`; the empty class space (no `Nonempty` instance is needed to
  state or apply the countable bound); a stage with no countability hypothesis (`ω₁` itself is
  excluded); the loss-plus-survivor adapter at the exact successor index `θ + 1`, feeding the
  ordinal bound; a `ℤ`-indexed instance of the general bound (stages with no least element and no
  ordinal) and a generic `Type 1` linear order of stages; nonvacuity of the countable bound on the
  countable ordinals.
* **Consequences of the countable bound.**  Under antitonicity its conclusion is equivalent to
  leaving the domain at `θ`; its hypotheses force an uncountable class space; with countable
  complements (not a hypothesis) it composes with `mk_eq_aleph_one_of_domains` to give `#X = ℵ₁`.
* **Negative controls, as actual counterexamples.**  (1) Singleton domain: nonemptiness and an
  ambient `Nontrivial` type do not suffice.  (2) Uniformity dropped.  (3) Isolation dropped.
  (4) Antitonicity dropped: the point returns at a later stage.  (5) Rank endpoint: under the
  convention "agreement for ranks strictly below the stage" the strict bound fails on `Bool`.
  (6) The bound is not attained and depends on the chosen isolating observation.
* **Semantic layer.**  `qrank_lt_omega1` on a quantified formula; the wrapper on an abstract
  isolated presentation; the consumer's call shape through the landed producer
  `isolatedPresentation_of_surjective` as a direct application; the per-class shape with local
  loss-plus-survivor witnesses, exclusion at the isolating sentence's rank and a strict bound at
  every stage.
* **Import closures.**  The `InfinitaryLogic` closure of `OrdinalCountability` is exactly
  `{OrdinalCountability, OrdinalUtil}`, that of `Lomega1omega.QuantifierRank` and that of
  `Descriptive.ScottDefinability` are pinned exactly (`[CLOSURE DRIFT]`).
* **Proof cones** (types and values, fail-closed).  The cones of the generic declarations contain
  no `FirstOrder` constant and no constant of a project module other than `OrdinalCountability`;
  the cones of the wrapper and of `qrank_lt_omega1` contain no constant of a `Scott`,
  `ScottProcess`, `Karp`, `Descriptive.BFEquivBorel` or `Conditional` module and no
  Scott-sentence, back-and-forth or potential-isomorphism name.  Positive controls: a guard
  theorem using `scottSentence_characterizes` is flagged by the generic check, and the
  consumer-chain regression is flagged by the wrapper check, its cone containing
  `scottSentence_characterizes` and `Karp` constants.  The cones of the imported modules are not
  the cones of the proofs: the wrapper's module imports the Scott and Karp theory.
* **Placement.**  Each export is declared in its intended module.

All exported declarations and all guard declarations use only the standard axioms (a separate
audit).  The OK line is printed only after every check.

Run with: lake env lean scripts/check_scott_separation_regressions.lean
-/
import InfinitaryLogic.Descriptive.ScottDefinability

open Lean InfinitaryLogic Set

universe u v w

noncomputable section

namespace ScottSeparationGuard

/-! ### Positive regressions: the generic layer -/

section Positive

/-- **Two-point class space**: isolation plus constant truth on the two-point domain `univ` is
incompatible with membership of the isolated point, hence `False`. -/
theorem two_point_false (Sat : Unit → Bool → Prop) (hiso : ∀ x, Sat () x ↔ x = true)
    (huniform : ∀ ⦃x y⦄, x ∈ (univ : Set Bool) → y ∈ univ → (Sat () x ↔ Sat () y)) : False :=
  notMem_of_isolating_of_uniform Sat hiso huniform ⟨true, trivial, false, trivial, by decide⟩
    trivial

/-- **The hypotheses are satisfiable**: on `Fin 3`, the domain `{1, 2}` of two other points, with
the isolated point `0` outside; the conclusion of the exclusion is then true. -/
theorem satisfiable_outside :
    (∀ x : Fin 3, x = 0 ↔ x = 0) ∧
      (∀ ⦃x y : Fin 3⦄, x ∈ ({1, 2} : Set (Fin 3)) → y ∈ ({1, 2} : Set (Fin 3)) →
        (x = 0 ↔ y = 0)) ∧
      ({1, 2} : Set (Fin 3)).Nontrivial ∧ (0 : Fin 3) ∉ ({1, 2} : Set (Fin 3)) := by
  have huniform : ∀ ⦃x y : Fin 3⦄, x ∈ ({1, 2} : Set (Fin 3)) → y ∈ ({1, 2} : Set (Fin 3)) →
      (x = 0 ↔ y = 0) := by
    intro x y hx hy
    simp only [mem_insert_iff, mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide
  have htwo : ({1, 2} : Set (Fin 3)).Nontrivial := ⟨1, by simp, 2, by simp, by decide⟩
  exact ⟨fun _ ↦ Iff.rfl, huniform, htwo,
    notMem_of_isolating_of_uniform (fun (_ : Unit) (x : Fin 3) ↦ x = 0) (φ := ())
      (fun _ ↦ Iff.rfl) huniform htwo⟩

/-- **Rank zero**, with no positivity assumption: the point lies in no domain. -/
theorem rank_zero_excluded {X : Type u} {F : Type v} (Sat : F → X → Prop)
    (rank : F → Ordinal.{0}) (D : Ordinal.{0} → Set X) (hanti : Antitone D) {q : X} {φ : F}
    (h0 : rank φ = 0) (hiso : ∀ x, Sat φ x ↔ x = q)
    (huniform : ∀ ⦃x y⦄, x ∈ D (rank φ) → y ∈ D (rank φ) → (Sat φ x ↔ Sat φ y))
    (htwo : (D (rank φ)).Nontrivial) (η : Ordinal.{0}) : q ∉ D η := fun hq ↦
  not_lt_zero (h0 ▸ stage_lt_rank_of_isolating Sat rank D hanti hiso huniform htwo hq)

/-- **Independent universes** (`Type 2` classes, `Type 0` observations), no `Nonempty X`: the
countable bound with the handoff's exact binders. -/
theorem independent_universes (X : Type 2) (F : Type) (Sat : F → X → Prop)
    (rank : F → Ordinal.{0}) (D : Ordinal.{0} → Set X) (hanti : Antitone D)
    (huniform : ∀ η, η < Ordinal.omega 1 → ∀ φ, rank φ ≤ η → ∀ ⦃x y⦄, x ∈ D η → y ∈ D η →
      (Sat φ x ↔ Sat φ y))
    (htwo : ∀ η, η < Ordinal.omega 1 → (D η).Nontrivial)
    (hisolate : ∀ q, ∃ φ, rank φ < Ordinal.omega 1 ∧ ∀ x, Sat φ x ↔ x = q) (q : X) :
    ∃ θ, θ < Ordinal.omega 1 ∧ ∀ η, q ∈ D η → η < θ :=
  exists_countable_strict_stage_bound_of_isolation Sat rank D hanti huniform htwo hisolate q

/-- **The empty class space**: the countable bound is stated and applied with no `Nonempty`
instance (its nonsingleton hypothesis is then unsatisfiable, so this is vacuous). -/
theorem empty_space (F : Type) (Sat : F → Empty → Prop) (rank : F → Ordinal.{0})
    (D : Ordinal.{0} → Set Empty) (hanti : Antitone D)
    (huniform : ∀ η, η < Ordinal.omega 1 → ∀ φ, rank φ ≤ η → ∀ ⦃x y⦄, x ∈ D η → y ∈ D η →
      (Sat φ x ↔ Sat φ y))
    (htwo : ∀ η, η < Ordinal.omega 1 → (D η).Nontrivial)
    (hisolate : ∀ q, ∃ φ, rank φ < Ordinal.omega 1 ∧ ∀ x, Sat φ x ↔ x = q) :
    ∀ q : Empty, ∃ θ, θ < Ordinal.omega 1 ∧ ∀ η, q ∈ D η → η < θ :=
  exists_countable_strict_stage_bound_of_isolation Sat rank D hanti huniform htwo hisolate

/-- **A stage with no countability hypothesis**: the countable bound excludes the point from the
domain at `ω₁` itself. -/
theorem uncountable_stage_excluded {X : Type u} {F : Type v} (Sat : F → X → Prop)
    (rank : F → Ordinal.{0}) (D : Ordinal.{0} → Set X) (hanti : Antitone D)
    (huniform : ∀ η, η < Ordinal.omega 1 → ∀ φ, rank φ ≤ η → ∀ ⦃x y⦄, x ∈ D η → y ∈ D η →
      (Sat φ x ↔ Sat φ y))
    (htwo : ∀ η, η < Ordinal.omega 1 → (D η).Nontrivial)
    (hisolate : ∀ q, ∃ φ, rank φ < Ordinal.omega 1 ∧ ∀ x, Sat φ x ↔ x = q) (q : X) :
    q ∉ D (Ordinal.omega 1) := fun hq ↦
  let ⟨_, hθ, hb⟩ :=
    exists_countable_strict_stage_bound_of_isolation Sat rank D hanti huniform htwo hisolate q
  (hb _ hq).not_gt hθ

/-- **Loss plus survivor** (guard-only adapter): `a ∈ D i \ D j` and `b ∈ D j` with `i ≤ j` give a
nonsingleton `D i`. -/
theorem nontrivial_of_loss_of_survivor {X : Type u} {ι : Type w} [Preorder ι]
    {D : ι → Set X} (hanti : Antitone D) {i j : ι} (hij : i ≤ j) {a b : X}
    (ha : a ∈ D i) (ha' : a ∉ D j) (hb : b ∈ D j) : (D i).Nontrivial :=
  ⟨a, ha, b, hanti hij hb, fun hab ↦ ha' (hab ▸ hb)⟩

/-- The adapter at the **exact successor index**: `a ∈ D θ \ D (θ + 1)`, `b ∈ D (θ + 1)`. -/
theorem nontrivial_of_succ_loss {X : Type u} {D : Ordinal.{0} → Set X} (hanti : Antitone D)
    {θ : Ordinal.{0}} {a b : X} (ha : a ∈ D θ) (ha' : a ∉ D (θ + 1)) (hb : b ∈ D (θ + 1)) :
    (D θ).Nontrivial :=
  nontrivial_of_loss_of_survivor hanti (Order.le_succ θ) ha ha' hb

/-- The adapter feeding the ordinal bound at `θ = rank φ`, for an arbitrary stage `η`. -/
theorem loss_survivor_bound {X : Type u} {F : Type v} (Sat : F → X → Prop)
    (rank : F → Ordinal.{0}) (D : Ordinal.{0} → Set X) (hanti : Antitone D) {q : X} {φ : F}
    (hiso : ∀ x, Sat φ x ↔ x = q)
    (huniform : ∀ ⦃x y⦄, x ∈ D (rank φ) → y ∈ D (rank φ) → (Sat φ x ↔ Sat φ y))
    {a b : X} (ha : a ∈ D (rank φ)) (ha' : a ∉ D (rank φ + 1)) (hb : b ∈ D (rank φ + 1))
    (η : Ordinal.{0}) (hq : q ∈ D η) : η < rank φ :=
  stage_lt_rank_of_isolating Sat rank D hanti hiso huniform
    (nontrivial_of_succ_loss hanti ha ha' hb) hq

/-- `ℤ`-indexed domains on `Fin 3`: everything at negative stages, `{1, 2}` from `0` on. -/
def Dz (η : ℤ) : Set (Fin 3) := {x | η < 0 ∨ x ≠ 0}

theorem Dz_antitone : Antitone Dz := fun _ _ hab _ hx ↦
  hx.imp (fun hb ↦ lt_of_le_of_lt hab hb) id

/-- **A `ℤ`-indexed instance of the general bound** (no least stage, no ordinal): the point `0`,
isolated by `x = 0` of rank `0`, lies only in negative stages, and does lie at `-1`. -/
theorem int_instance : (∀ η : ℤ, (0 : Fin 3) ∈ Dz η → η < 0) ∧ (0 : Fin 3) ∈ Dz (-1) := by
  have huniform : ∀ ⦃x y : Fin 3⦄, x ∈ Dz 0 → y ∈ Dz 0 → (x = 0 ↔ y = 0) := fun x y hx hy ↦
    have hx' : x ≠ 0 := hx.resolve_left (lt_irrefl 0)
    have hy' : y ≠ 0 := hy.resolve_left (lt_irrefl 0)
    ⟨fun h ↦ absurd h hx', fun h ↦ absurd h hy'⟩
  have htwo : (Dz 0).Nontrivial := ⟨1, Or.inr (by decide), 2, Or.inr (by decide), by decide⟩
  exact ⟨fun η hq ↦ lt_rank_of_isolating_of_antitone (fun (_ : Unit) (x : Fin 3) ↦ x = 0)
      (fun _ ↦ (0 : ℤ)) Dz Dz_antitone (φ := ()) (fun _ ↦ Iff.rfl) huniform htwo hq,
    Or.inl (by decide)⟩

/-- **A generic `Type 1` linear order of stages**, with `Type 2` observations: the general bound
applies with no ordinal and no well-foundedness. -/
theorem type1_instance {ι : Type 1} [LinearOrder ι] {X : Type} {F : Type 2} (Sat : F → X → Prop)
    (rank : F → ι) (D : ι → Set X) (hanti : Antitone D) {q : X} {φ : F}
    (hiso : ∀ x, Sat φ x ↔ x = q)
    (huniform : ∀ ⦃x y⦄, x ∈ D (rank φ) → y ∈ D (rank φ) → (Sat φ x ↔ Sat φ y))
    (htwo : (D (rank φ)).Nontrivial) {η : ι} (hq : q ∈ D η) : η < rank φ :=
  lt_rank_of_isolating_of_antitone Sat rank D hanti hiso huniform htwo hq

/-- The ordinal form is literally the instance of the general one. -/
theorem ordinal_is_instance {X : Type u} {F : Type v} (Sat : F → X → Prop)
    (rank : F → Ordinal.{0}) (D : Ordinal.{0} → Set X) (hanti : Antitone D) {q : X} {φ : F}
    (hiso : ∀ x, Sat φ x ↔ x = q)
    (huniform : ∀ ⦃x y⦄, x ∈ D (rank φ) → y ∈ D (rank φ) → (Sat φ x ↔ Sat φ y))
    (htwo : (D (rank φ)).Nontrivial) {η : Ordinal.{0}} (hq : q ∈ D η) :
    stage_lt_rank_of_isolating Sat rank D hanti hiso huniform htwo hq =
      lt_rank_of_isolating_of_antitone Sat rank D hanti hiso huniform htwo hq :=
  rfl

/-- **Nonvacuity of the countable bound**: on the countable ordinals, with the rank tails as
domains, observations the points themselves (`Sat φ x := x = φ`) and `rank φ := φ + 1`, every
hypothesis holds. -/
theorem c_nonvacuous :
    let X := Set.Iio (Ordinal.omega 1 : Ordinal.{0})
    let D : Ordinal.{0} → Set X := rankTail (fun x : X ↦ x.1)
    let Sat : X → X → Prop := fun φ x ↦ x = φ
    let rank : X → Ordinal.{0} := fun φ ↦ φ.1 + 1
    Antitone D ∧
      (∀ η, η < Ordinal.omega 1 → ∀ φ, rank φ ≤ η → ∀ ⦃x y⦄, x ∈ D η → y ∈ D η →
        (Sat φ x ↔ Sat φ y)) ∧
      (∀ η, η < Ordinal.omega 1 → (D η).Nontrivial) ∧
      (∀ q, ∃ φ, rank φ < Ordinal.omega 1 ∧ ∀ x, Sat φ x ↔ x = q) := by
  intro X D Sat rank
  have hlim := Cardinal.isSuccLimit_omega (1 : Ordinal)
  refine ⟨rankTail_antitone (fun x : X ↦ x.1), ?_, ?_, ?_⟩
  · intro η _ φ hφ x y hx hy
    have hx' : η ≤ x.1 := hx
    have hy' : η ≤ y.1 := hy
    have hφη : φ.1 < η := (Order.lt_add_one_iff.mpr le_rfl).trans_le hφ
    constructor
    · intro h; exact absurd (h ▸ hx' : η ≤ φ.1) (not_le.mpr hφη)
    · intro h; exact absurd (h ▸ hy' : η ≤ φ.1) (not_le.mpr hφη)
  · intro η hη
    refine ⟨⟨η, hη⟩, (le_refl η : η ≤ η), ⟨η + 1, hlim.add_one_lt hη⟩,
      (Order.le_succ η : η ≤ η + 1), ?_⟩
    intro h
    exact (Order.lt_add_one_iff.mpr le_rfl).ne (congrArg Subtype.val h)
  · intro q
    exact ⟨q, hlim.add_one_lt q.2, fun _ ↦ Iff.rfl⟩

/-- The countable bound on the nonvacuity instance: the point `q` leaves by stage `q + 1`. -/
theorem c_nonvacuous_applied (q : Set.Iio (Ordinal.omega 1 : Ordinal.{0})) :
    ∃ θ, θ < Ordinal.omega 1 ∧ ∀ η, q ∈ rankTail (fun x : Set.Iio (Ordinal.omega 1) ↦ x.1) η →
      η < θ :=
  let h := c_nonvacuous
  exists_countable_strict_stage_bound_of_isolation (fun φ x ↦ x = φ) (fun φ ↦ φ.1 + 1) _ h.1
    h.2.1 h.2.2.1 h.2.2.2 q

end Positive

/-! ### Consequences of the countable bound -/

section Consequences

/-- Under antitonicity, "every stage containing `q` is below `θ`" is "`q ∉ D θ`", the
every-point-leaves premise of `mk_le_aleph_one_of_domains` and `mk_eq_aleph_one_of_domains`. -/
theorem forall_lt_iff_notMem {X : Type u} {D : Ordinal.{0} → Set X} (hanti : Antitone D)
    {q : X} {θ : Ordinal.{0}} : (∀ η, q ∈ D η → η < θ) ↔ q ∉ D θ :=
  ⟨fun h hq ↦ lt_irrefl θ (h θ hq), fun h _ hq ↦ lt_of_not_ge fun hle ↦ h (hanti hle hq)⟩

/-- Countable strict bounds and nonempty countable stages force an uncountable space. -/
theorem not_countable_of_strict_stage_bounds {X : Type u} (D : Ordinal.{0} → Set X)
    (hne : ∀ η, η < Ordinal.omega 1 → (D η).Nonempty)
    (hbound : ∀ q : X, ∃ θ, θ < Ordinal.omega 1 ∧ ∀ η, q ∈ D η → η < θ) :
    ¬ Countable X := by
  intro hX
  choose θ hθ hb using hbound
  have hs : (⨆ q, θ q) < Ordinal.omega 1 := Ordinal.iSup_lt_omega_one hθ
  obtain ⟨x, hx⟩ := hne _ hs
  have hbdd : BddAbove (Set.range θ) := ⟨Ordinal.omega 1, by rintro _ ⟨q, rfl⟩; exact (hθ q).le⟩
  exact (hb x _ hx).not_ge (le_ciSup hbdd x)

/-- **The hypotheses of the countable bound force an uncountable class space** (they are not
assumed to). -/
theorem not_countable_of_isolation {X : Type u} {F : Type v} (Sat : F → X → Prop)
    (rank : F → Ordinal.{0}) (D : Ordinal.{0} → Set X) (hanti : Antitone D)
    (huniform : ∀ η, η < Ordinal.omega 1 → ∀ φ, rank φ ≤ η → ∀ ⦃x y⦄, x ∈ D η → y ∈ D η →
      (Sat φ x ↔ Sat φ y))
    (htwo : ∀ η, η < Ordinal.omega 1 → (D η).Nontrivial)
    (hisolate : ∀ q, ∃ φ, rank φ < Ordinal.omega 1 ∧ ∀ x, Sat φ x ↔ x = q) :
    ¬ Countable X :=
  not_countable_of_strict_stage_bounds D (fun η hη ↦ (htwo η hη).nonempty)
    (exists_countable_strict_stage_bound_of_isolation Sat rank D hanti huniform htwo hisolate)

/-- **Composition with `mk_eq_aleph_one_of_domains`**: with countable complements (not a
hypothesis of the bound) the class space has cardinality exactly `ℵ₁`. -/
theorem mk_eq_aleph_one_of_isolation {X : Type u} {F : Type v} (Sat : F → X → Prop)
    (rank : F → Ordinal.{0}) (D : Ordinal.{0} → Set X) (hanti : Antitone D)
    (huniform : ∀ η, η < Ordinal.omega 1 → ∀ φ, rank φ ≤ η → ∀ ⦃x y⦄, x ∈ D η → y ∈ D η →
      (Sat φ x ↔ Sat φ y))
    (htwo : ∀ η, η < Ordinal.omega 1 → (D η).Nontrivial)
    (hisolate : ∀ q, ∃ φ, rank φ < Ordinal.omega 1 ∧ ∀ x, Sat φ x ↔ x = q)
    (hcompl : ∀ β, β < Ordinal.omega 1 → (D β)ᶜ.Countable) :
    Cardinal.mk X = Cardinal.aleph 1 :=
  mk_eq_aleph_one_of_domains D hanti hcompl (fun β hβ ↦ (htwo β hβ).nonempty) fun q ↦
    let ⟨θ, hθ, h⟩ :=
      exists_countable_strict_stage_bound_of_isolation Sat rank D hanti huniform htwo hisolate q
    ⟨θ, hθ, (forall_lt_iff_notMem hanti).mp h⟩

end Consequences

/-! ### Negative controls: actual counterexamples -/

section Negative

/-- **(1) Mere nonemptiness is insufficient**, and so is an ambient nontrivial type: on `Bool`,
`D = {true}` and `Sat φ x := x = true`; isolation and uniformity hold, yet `true ∈ D`. -/
theorem neg_singleton :
    Nontrivial Bool ∧ ({true} : Set Bool).Nonempty ∧ (∀ x : Bool, x = true ↔ x = true) ∧
      (∀ ⦃x y : Bool⦄, x ∈ ({true} : Set Bool) → y ∈ ({true} : Set Bool) →
        (x = true ↔ y = true)) ∧
      true ∈ ({true} : Set Bool) ∧ ¬ ({true} : Set Bool).Nontrivial := by
  refine ⟨inferInstance, ⟨true, rfl⟩, fun _ ↦ Iff.rfl, ?_, rfl, ?_⟩
  · intro x y hx hy
    simp only [mem_singleton_iff] at hx hy
    subst hx hy
    exact Iff.rfl
  · exact not_nontrivial_singleton

/-- **(2) Uniformity is essential**: on the two-point domain `univ : Set Bool` containing
`q = true`, the isolating predicate `x = true` is not constant. -/
theorem neg_uniformity :
    (univ : Set Bool).Nontrivial ∧ true ∈ (univ : Set Bool) ∧ (∀ x : Bool, x = true ↔ x = true) ∧
      ¬ (∀ ⦃x y : Bool⦄, x ∈ (univ : Set Bool) → y ∈ univ → (x = true ↔ y = true)) :=
  ⟨⟨true, trivial, false, trivial, by decide⟩, trivial, fun _ ↦ Iff.rfl, fun h ↦
    Bool.false_ne_true ((h (x := true) (y := false) trivial trivial).mp rfl)⟩

/-- **(3) Isolation is essential**: a constantly true observation is uniform on the two-point
domain `univ`, which contains both points, and isolates neither. -/
theorem neg_isolation :
    (∀ ⦃x y : Bool⦄, x ∈ (univ : Set Bool) → y ∈ univ → (True ↔ True)) ∧
      (univ : Set Bool).Nontrivial ∧ (∀ q : Bool, q ∈ (univ : Set Bool)) ∧
      (∀ q : Bool, ¬ ∀ x : Bool, True ↔ x = q) := by
  refine ⟨fun _ _ _ _ ↦ Iff.rfl, ⟨true, trivial, false, trivial, by decide⟩, fun _ ↦ trivial,
    fun q h ↦ ?_⟩
  cases q
  · exact Bool.true_eq_false ▸ ((h true).mp trivial)
  · exact Bool.false_ne_true ((h false).mp trivial)

/-- The domains of the antitonicity counterexample: `{1, 2}` at stage `0`, everything after. -/
def Dgrow (η : Ordinal.{0}) : Set (Fin 3) := {x | η = 0 → x ≠ 0}

/-- **(4) Antitonicity is essential**: with `q = 0`, `rank φ = 0` and `Sat φ x := x = 0`, every
hypothesis of the ordinal bound holds at `rank φ` except antitonicity, yet `q ∈ D 1` and
`¬ 1 < 0`. -/
theorem neg_antitone :
    ¬ Antitone Dgrow ∧ (∀ x : Fin 3, x = 0 ↔ x = 0) ∧
      (∀ ⦃x y : Fin 3⦄, x ∈ Dgrow 0 → y ∈ Dgrow 0 → (x = 0 ↔ y = 0)) ∧ (Dgrow 0).Nontrivial ∧
      (0 : Fin 3) ∈ Dgrow 1 ∧ ¬ (1 : Ordinal.{0}) < 0 := by
  refine ⟨fun h ↦ ?_, fun _ ↦ Iff.rfl, ?_, ⟨1, by simp [Dgrow], 2, by simp [Dgrow], by decide⟩,
    fun h10 ↦ absurd h10 one_ne_zero, by simp⟩
  · have h1 : (0 : Fin 3) ∈ Dgrow 1 := fun h10 ↦ absurd h10 one_ne_zero
    exact (h (zero_le_one : (0 : Ordinal.{0}) ≤ 1) h1) rfl rfl
  · intro x y hx hy
    exact ⟨fun h ↦ absurd h (hx rfl), fun h ↦ absurd h (hy rfl)⟩

/-- **(5) The rank endpoint matters.**  Under the convention "agreement at stage `η` only for
observations of rank strictly below `η`", take `Bool`, `D η = univ` for `η ≤ 1` and `∅` above,
and `x = true` of rank `1`.  The domains are antitone, the observation isolates `true`, the
strict-convention agreement at `rank φ = 1` holds (vacuously for the single observation), the
domain at `1` is nonsingleton, yet `true ∈ D 1` and `¬ 1 < 1`: the strict bound is not
retained. -/
theorem neg_rank_endpoint :
    let D : Ordinal.{0} → Set Bool := fun η ↦ {_x | η ≤ 1}
    let rank : Unit → Ordinal.{0} := fun _ ↦ 1
    let Sat : Unit → Bool → Prop := fun _ x ↦ x = true
    Antitone D ∧ (∀ x, Sat () x ↔ x = true) ∧
      (∀ ψ, rank ψ < rank () → ∀ ⦃x y⦄, x ∈ D (rank ()) → y ∈ D (rank ()) →
        (Sat ψ x ↔ Sat ψ y)) ∧
      (D (rank ())).Nontrivial ∧ true ∈ D (rank ()) ∧ ¬ rank () < rank () := by
  intro D rank Sat
  exact ⟨fun _ _ hab _ hx ↦ hab.trans hx, fun _ ↦ Iff.rfl, fun _ h ↦ absurd h (lt_irrefl _),
    ⟨true, (le_refl (1 : Ordinal.{0})), false, (le_refl (1 : Ordinal.{0})), by decide⟩,
    (le_refl (1 : Ordinal.{0})), lt_irrefl _⟩

/-- **(6) A bound, not an attained stage, and not intrinsic.**  On `Unit` with `D η = univ` iff
`η = 0`, every `n : ℕ` (an observation of rank `n`) isolates the point.  The point's stages stop
at `0`, while the bound from the observation `7` is `7`: the bound depends on the chosen
isolating observation and is not attained. -/
theorem bound_not_attained :
    let D : Ordinal.{0} → Set Unit := fun η ↦ {_x | η = 0}
    Antitone D ∧ (∀ (_n : ℕ) (x : Unit), x = () ↔ x = ()) ∧ () ∈ D 0 ∧
      (∀ η, () ∈ D η → η = 0) ∧ ((7 : ℕ) : Ordinal.{0}) = 7 ∧ ¬ () ∈ D 7 := by
  intro D
  refine ⟨fun a b hab x hx ↦ ?_, fun _ _ ↦ Iff.rfl, rfl, fun _ h ↦ h, rfl, fun h ↦ ?_⟩
  · have hb : b = 0 := hx
    subst hb
    exact le_antisymm hab zero_le
  · exact OfNat.ofNat_ne_zero _ (h : (7 : Ordinal.{0}) = 0)

end Negative

/-! ### The semantic layer -/

section Semantic

open FirstOrder Language

/-- **Countable rank**, applied to a formula and to a sentence of an arbitrary language. -/
theorem qrank_countable {L : Language.{u, v}} {α : Type w} {n : ℕ}
    (φ : L.BoundedFormulaω α (n + 1)) (σ : L.Sentenceω) :
    (BoundedFormulaω.all φ).qrank < Ordinal.omega 1 ∧ σ.qrank < Ordinal.omega 1 :=
  ⟨BoundedFormulaω.qrank_lt_omega1 _, Sentenceω.qrank_lt_omega1 σ⟩

/-- **The wrapper on an abstract isolated presentation**, a direct application. -/
theorem wrapper_abstract {L : Language.{u, v}} {Q : Type w} {truth : L.Sentenceω → Q → Prop}
    (hisol : IsolatedPresentation truth) (D : Ordinal.{0} → Set Q) (hanti : Antitone D)
    (huniform : ∀ η, η < Ordinal.omega 1 → ∀ φ : L.Sentenceω, φ.qrank ≤ η →
      ∀ ⦃x y⦄, x ∈ D η → y ∈ D η → (truth φ x ↔ truth φ y))
    (htwo : ∀ η, η < Ordinal.omega 1 → (D η).Nontrivial) (q : Q) :
    (∃ σ : L.Sentenceω, σ.qrank < Ordinal.omega 1 ∧ ∀ s, truth σ s ↔ s = q) ∧
      ∃ θ, θ < Ordinal.omega 1 ∧ ∀ η, q ∈ D η → η < θ :=
  ⟨hisol.exists_qrank_lt q, hisol.exists_countable_strict_stage_bound D hanti huniform htwo q⟩

/-- **The consumer's call shape** through the landed producer `isolatedPresentation_of_surjective`:
the presentation data, the uniform-agreement theorem and the nonsingleton domains, as one direct
application. -/
theorem consumer_call_shape {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] {X : Type u} {Q : Type w}
    (codes : X → StructureSpace L) (classOf : X → Q) (honto : Function.Surjective classOf)
    (hiso : ∀ x y, (structureIsoSetoid L).r (codes x) (codes y) → classOf x = classOf y)
    (truth : L.Sentenceω → Q → Prop)
    (htruth : ∀ φ x, truth φ (classOf x) ↔ codes x ∈ ModelsOf φ)
    (D : Ordinal.{0} → Set Q) (hanti : Antitone D)
    (hagree : ∀ η, η < Ordinal.omega 1 → ∀ φ : L.Sentenceω, φ.qrank ≤ η →
      ∀ ⦃x y⦄, x ∈ D η → y ∈ D η → (truth φ x ↔ truth φ y))
    (htwo : ∀ η, η < Ordinal.omega 1 → (D η).Nontrivial) (q : Q) :
    ∃ θ, θ < Ordinal.omega 1 ∧ ∀ η, q ∈ D η → η < θ :=
  (isolatedPresentation_of_surjective codes classOf honto hiso truth htruth)
    |>.exists_countable_strict_stage_bound D hanti hagree htwo q

/-- **The per-class shape** with local loss-plus-survivor witnesses at `θ := σ.qrank` and the
successor index `θ + 1`: exclusion at the isolating sentence's rank, and a strict bound at every
stage, countable or not. -/
theorem consumer_per_class {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] {X : Type u} {Q : Type w}
    (codes : X → StructureSpace L) (classOf : X → Q) (honto : Function.Surjective classOf)
    (hiso : ∀ x y, (structureIsoSetoid L).r (codes x) (codes y) → classOf x = classOf y)
    (truth : L.Sentenceω → Q → Prop)
    (htruth : ∀ φ x, truth φ (classOf x) ↔ codes x ∈ ModelsOf φ)
    (D : Ordinal.{0} → Set Q) (hanti : Antitone D)
    (hagree : ∀ η, η < Ordinal.omega 1 → ∀ φ : L.Sentenceω, φ.qrank ≤ η →
      ∀ ⦃x y⦄, x ∈ D η → y ∈ D η → (truth φ x ↔ truth φ y))
    (hloss : ∀ θ, ∃ a b, a ∈ D θ ∧ a ∉ D (θ + 1) ∧ b ∈ D (θ + 1)) (q : Q) :
    ∃ σ : L.Sentenceω, σ.qrank < Ordinal.omega 1 ∧ q ∉ D σ.qrank ∧
      ∀ η, q ∈ D η → η < σ.qrank := by
  obtain ⟨σ, hσ⟩ := isolatedPresentation_of_surjective codes classOf honto hiso truth htruth q
  have hσω : σ.qrank < Ordinal.omega 1 := Sentenceω.qrank_lt_omega1 σ
  obtain ⟨a, b, ha, ha', hb⟩ := hloss σ.qrank
  have htwo : (D σ.qrank).Nontrivial := nontrivial_of_succ_loss hanti ha ha' hb
  exact ⟨σ, hσω,
    notMem_of_isolating_of_uniform truth hσ (hagree σ.qrank hσω σ le_rfl) htwo,
    fun η hq ↦ stage_lt_rank_of_isolating truth (fun φ ↦ φ.qrank) D hanti hσ
      (hagree σ.qrank hσω σ le_rfl) htwo hq⟩

/-- **Positive control** for the cone checks: a theorem whose proof uses
`scottSentence_characterizes`. -/
theorem scott_control {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ l, L.Relations l)]
    (M : Type) [L.Structure M] [Countable M] :
    (scottSentence (L := L) M).realize_as_sentence M → Nonempty (M ≃[L] M) :=
  (scottSentence_characterizes M M).mp

end Semantic

end ScottSeparationGuard

end

/-! ### Closures, cones, placement and axioms -/

namespace ScottSeparationGuard

/-- Prefix a list of names with `InfinitaryLogic`. -/
def ilm (l : List Name) : List Name := l.map (`InfinitaryLogic ++ ·)

/-- Prefix a list of names with `FirstOrder.Language`. -/
def fol (l : List Name) : List Name := l.map (`FirstOrder.Language ++ ·)

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

/-- The project modules of the closure of `m`, sorted. -/
def projectClosure (env : Environment) (m : Name) : List Name :=
  ((importClosure env m).toList.filter (Name.isPrefixOf `InfinitaryLogic)).mergeSort
    fun a b ↦ a.toString ≤ b.toString

/-- The exact project closure of `OrdinalCountability`. -/
def ordinalCountabilityClosure : List Name := ilm [`OrdinalCountability, `OrdinalUtil]

/-- The exact project closure of `Lomega1omega.QuantifierRank`. -/
def quantifierRankClosure : List Name := ilm
  [`Lomega1omega.Operations, `Lomega1omega.QuantifierRank, `Lomega1omega.Semantics,
   `Lomega1omega.Syntax, `Util]

/-- The exact project closure of `Descriptive.ScottDefinability`, measured when the wrapper
landed (it grew by `OrdinalCountability` only).  Extending it is a deliberate decision. -/
def scottDefinabilityClosure : List Name := ilm
  [`Combinatorics.EndHomogeneousErdosRado, `Combinatorics.FiniteArityErdosRadoInduction,
   `Combinatorics.InfiniteRamsey, `Combinatorics.InfiniteRamseyFamily,
   `Combinatorics.PairErdosRadoGeneral, `Descriptive.AnalyticTree, `Descriptive.CantorAntichain,
   `Descriptive.CodeTransport, `Descriptive.CountableSplits, `Descriptive.InvariantMeasurableSpace,
   `Descriptive.InvariantSeparation, `Descriptive.LogicAction, `Descriptive.LopezEscobar,
   `Descriptive.LopezEscobarEasy, `Descriptive.Measurable, `Descriptive.ModelClassStandardBorel,
   `Descriptive.PerfectAntichain, `Descriptive.PermPolishGroup, `Descriptive.PermTopology,
   `Descriptive.Polish, `Descriptive.PolishAction, `Descriptive.QueryCode,
   `Descriptive.SatisfactionBorel, `Descriptive.SatisfactionBorelOn,
   `Descriptive.ScottDefinability, `Descriptive.SentenceObservables, `Descriptive.SentenceRecovery,
   `Descriptive.SentenceSplits, `Descriptive.SmallVocabulary, `Descriptive.SmallVocabularyLift,
   `Descriptive.SmallVocabularyTransport, `Descriptive.StructureIsoSetoid,
   `Descriptive.StructureSpace, `Descriptive.Topology, `Karp.PotentialIso, `Lomega1omega.Depth,
   `Lomega1omega.Entailment, `Lomega1omega.FiniteQuantification, `Lomega1omega.Fragment,
   `Lomega1omega.OpenBoundsSemantics, `Lomega1omega.Operations, `Lomega1omega.QuantifierClass,
   `Lomega1omega.QuantifierRank, `Lomega1omega.Semantics, `Lomega1omega.Syntax,
   `Lomega1omega.Theory, `Methods.ConstantAbstraction, `Methods.ConstantInstances,
   `Methods.ConstantSupport, `Methods.EM.FragmentAdapter, `Methods.EM.Indiscernible,
   `Methods.EM.Realization, `Methods.EM.TailAdapter, `Methods.EM.Template,
   `Methods.GeneratedSublanguage, `Methods.Henkin.ConsistencyProperty,
   `Methods.Henkin.Construction, `Methods.Henkin.CountableCompletion.ConsistencyPropertyEqOn,
   `Methods.Henkin.CountableCompletion.FairEnumeration,
   `Methods.Henkin.CountableCompletion.GeneratedUniverse,
   `Methods.Henkin.CountableCompletion.QuotientTermModel,
   `Methods.Henkin.CountableCompletion.QuotientTruthLemma,
   `Methods.Interpolation.BaseOccurrenceProjections, `Methods.Interpolation.ConstantElimination,
   `Methods.Interpolation.CraigRelational, `Methods.Interpolation.CraigSeparation,
   `Methods.Interpolation.CraigSublanguage, `Methods.Interpolation.GraphAxioms,
   `Methods.Interpolation.GraphLanguage, `Methods.Interpolation.GraphReconstruction,
   `Methods.Interpolation.Inseparability, `Methods.Interpolation.InseparablePairFamily,
   `Methods.Interpolation.PairedInsepFamily, `Methods.Interpolation.PairedInseparability,
   `Methods.Interpolation.QuantifierRoundTrip, `Methods.Interpolation.Relationalize,
   `Methods.Interpolation.RootGate, `Methods.Interpolation.TermGraph,
   `Methods.LanguageMapOccurrence, `Methods.LocalColimit, `Methods.LocalEMContext,
   `Methods.LocalEMFamily, `Methods.LocalEMSupport, `Methods.LocalEMTemplateRealization,
   `Methods.LocalEMTruth, `Methods.LocalEMTruthLemma, `Methods.LocalSkolem,
   `Methods.LocalSkolemUniversal, `Methods.LocalTower, `Methods.LopezEscobar.CodeClass,
   `Methods.LopezEscobar.Disjoint, `Methods.LopezEscobar.FunctionalTheta,
   `Methods.LopezEscobar.PCMem, `Methods.LopezEscobar.PCSentence,
   `Methods.LopezEscobar.RelationalizeSpike, `Methods.LopezEscobar.Separation,
   `Methods.LopezEscobar.SharedDecoder, `Methods.LopezEscobar.StandardModel,
   `Methods.LopezEscobar.TaggedGlue, `Methods.LopezEscobar.WitnessLang, `Methods.MarkerStage,
   `Methods.SchemaCompletion, `Methods.SchemaOmegaWitness, `Methods.Skolem, `Methods.SkolemClosure,
   `Methods.SkolemColimit, `Methods.SymbSublangExpansion, `Methods.TailIndiscernible,
   `ModelTheory.AElementary, `ModelTheory.FragmentLowenheimSkolem,
   `ModelTheory.HanfSpectrum.CardinalBounds, `ModelTheory.PCClass, `OrdinalCountability,
   `OrdinalUtil, `Scott.AtomicDiagram, `Scott.BackAndForth, `Scott.Formula, `Scott.RefinementCount,
   `Scott.Sentence, `Topology.Perfect, `Util]

/-- The generic declarations (section "Separation by an isolating observation"). -/
def genericRoots : List Name :=
  ilm [`notMem_of_isolating_of_uniform, `lt_rank_of_isolating_of_antitone,
    `stage_lt_rank_of_isolating, `exists_countable_strict_stage_bound_of_isolation]

/-- The countable-rank declarations. -/
def qrankRoots : List Name :=
  fol [`BoundedFormulaω.qrank_lt_omega1, `Sentenceω.qrank_lt_omega1]

/-- The wrapper declarations. -/
def wrapperRoots : List Name :=
  fol [`IsolatedPresentation.exists_qrank_lt,
    `IsolatedPresentation.exists_countable_strict_stage_bound]

/-- Where each export must be declared. -/
def placement : List (List Name × Name) :=
  [(genericRoots, `InfinitaryLogic.OrdinalCountability),
   (qrankRoots, `InfinitaryLogic.Lomega1omega.QuantifierRank),
   (wrapperRoots, `InfinitaryLogic.Descriptive.ScottDefinability)]

/-- Module prefixes the cones of the wrapper and of the countable rank may not reach. -/
def forbiddenModulePrefixes : List Name :=
  ilm [`Scott, `ScottProcess, `Karp, `Descriptive.BFEquivBorel, `Conditional]

/-- Name fragments the cones of the wrapper and of the countable rank may not contain. -/
def forbiddenNameFragments : List String :=
  ["scottSentence", "scottFormula", "BFEquiv", "BackAndForth", "PotentialIso",
   "stabilizationOrdinal", "countableRefinementHypothesis"]

/-- The guard's declarations whose axioms are audited. -/
def guardDecls : List Name :=
  [`two_point_false, `satisfiable_outside, `rank_zero_excluded, `independent_universes,
   `empty_space, `uncountable_stage_excluded, `nontrivial_of_loss_of_survivor,
   `nontrivial_of_succ_loss, `loss_survivor_bound, `Dz_antitone, `int_instance, `type1_instance,
   `ordinal_is_instance, `c_nonvacuous, `c_nonvacuous_applied, `forall_lt_iff_notMem,
   `not_countable_of_strict_stage_bounds, `not_countable_of_isolation,
   `mk_eq_aleph_one_of_isolation, `neg_singleton, `neg_uniformity, `neg_isolation,
   `neg_antitone, `neg_rank_endpoint, `bound_not_attained, `qrank_countable, `wrapper_abstract,
   `consumer_call_shape, `consumer_per_class, `scott_control].map (`ScottSeparationGuard ++ ·)

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- The constants a declaration refers to: its type, its value (theorem, definition and opaque
bodies alike), and the constructors, recursor rules and mutual families of inductive data. -/
def refs (ci : ConstantInfo) : NameSet := Id.run do
  let mut s := ci.type.getUsedConstantsAsSet
  match ci with
  | .defnInfo v => s := s ++ v.value.getUsedConstantsAsSet
  | .thmInfo v => s := s ++ v.value.getUsedConstantsAsSet
  | .opaqueInfo v => s := s ++ v.value.getUsedConstantsAsSet
  | .inductInfo v => s := s ++ .ofList v.ctors ++ .ofList v.all
  | .ctorInfo v => s := s.insert v.induct
  | .recInfo v =>
    s := s ++ .ofList v.all
    for r in v.rules do s := s ++ r.rhs.getUsedConstantsAsSet
  | .axiomInfo _ | .quotInfo _ => pure ()
  return s

/-- The transitive constant cone of `root`, failing closed on any constant that is not in the
environment. -/
def cone (env : Environment) (root : Name) : Except String NameSet := do
  let mut visited : NameSet := {}
  let mut stack : Array Name := #[root]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then
      continue
    visited := visited.insert n
    let some ci := env.find? n
      | throw s!"[UNKNOWN CONSTANT] {n} (reached from {root}) is not in the environment"
    for m in refs ci do
      unless visited.contains m do
        stack := stack.push m
  return visited

/-- The module declaring a constant. -/
def moduleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  return env.header.moduleNames[idx.toNat]!

/-- The cone of a root, as a command. -/
def coneOf (root : Name) : Elab.Command.CommandElabM NameSet := do
  let env ← getEnv
  unless (env.find? root).isSome do throwError "[UNKNOWN ROOT] {root}"
  match cone env root with
  | .ok c => pure c
  | .error e => throwError e

/-- The generic violations of a cone: `FirstOrder` constants, and constants of a project module
other than `OrdinalCountability`. -/
def genericViolations (env : Environment) (c : NameSet) : List Name × List (Name × Name) :=
  (c.toList.filter (Name.isPrefixOf `FirstOrder),
   c.toList.filterMap fun n ↦ do
     let m ← moduleOf env n
     if (`InfinitaryLogic).isPrefixOf m && m != `InfinitaryLogic.OrdinalCountability then
       some (n, m) else none)

/-- The Scott violations of a cone: constants of forbidden modules and forbidden names. -/
def scottViolations (env : Environment) (c : NameSet) : List (Name × Name) × List Name :=
  (c.toList.filterMap fun n ↦ do
     let m ← moduleOf env n
     if forbiddenModulePrefixes.any (·.isPrefixOf m) then some (n, m) else none,
   c.toList.filter fun n ↦
     forbiddenNameFragments.any fun s ↦ (n.toString.splitOn s).length ≠ 1)

/-- **Closures**: exact project closures of the three host modules. -/
def checkClosures : Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  for (m, expected) in [(`InfinitaryLogic.OrdinalCountability, ordinalCountabilityClosure),
      (`InfinitaryLogic.Lomega1omega.QuantifierRank, quantifierRankClosure),
      (`InfinitaryLogic.Descriptive.ScottDefinability, scottDefinabilityClosure)] do
    unless (env.getModuleIdx? m).isSome do throwError "module {m} is not in the environment"
    let got := projectClosure env m
    let exp := expected.mergeSort fun a b ↦ a.toString ≤ b.toString
    unless got == exp do
      throwError "[CLOSURE DRIFT] the project closure of {m} is {got} (size {got.length}), \
        expected {exp} (size {exp.length})"

/-- **Placement**: each export is declared in its intended module. -/
def checkPlacement : Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  for (roots, m) in placement do
    for n in roots do
      unless (env.find? n).isSome do throwError "[UNKNOWN ROOT] {n}"
      unless moduleOf env n == some m do
        throwError "[PLACEMENT] {n} is declared in {moduleOf env n}, expected {m}"

/-- **Cones**: the generic layer is logic-free, the wrapper and the countable rank are free of
Scott theory, and both checks flag their positive controls. -/
def checkCones : Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  for r in genericRoots do
    let (fo, mods) := genericViolations env (← coneOf r)
    unless fo.isEmpty do throwError "[LOGIC IN GENERIC CONE] {r} reaches {fo}"
    unless mods.isEmpty do throwError "[PROJECT IN GENERIC CONE] {r} reaches {mods}"
  -- positive control: the generic check flags a proof through `scottSentence_characterizes`
  let ctl ← coneOf `ScottSeparationGuard.scott_control
  unless ctl.contains `FirstOrder.Language.scottSentence_characterizes do
    throwError "[CONTROL] the control's cone misses scottSentence_characterizes"
  let (fo, mods) := genericViolations env ctl
  if fo.isEmpty || mods.isEmpty then
    throwError "[VACUOUS CHECK] the generic check does not flag the Scott control"
  for r in qrankRoots ++ wrapperRoots do
    let (mods, names) := scottViolations env (← coneOf r)
    unless mods.isEmpty do throwError "[SCOTT IN WRAPPER CONE] {r} reaches {mods}"
    unless names.isEmpty do throwError "[SCOTT IN WRAPPER CONE] {r} reaches {names}"
  -- the wrapper does use the generic layer and the countable rank
  let w ← coneOf `FirstOrder.Language.IsolatedPresentation.exists_countable_strict_stage_bound
  for n in [`InfinitaryLogic.exists_countable_strict_stage_bound_of_isolation,
      `FirstOrder.Language.Sentenceω.qrank_lt_omega1] do
    unless w.contains n do throwError "[MISSING ROUTE] the wrapper's cone misses {n}"
  -- the consumer chain does reach Scott theory, and the wrapper check flags it
  let chain ← coneOf `ScottSeparationGuard.consumer_call_shape
  for n in [`FirstOrder.Language.scottSentence_characterizes,
      `FirstOrder.Language.isolatedPresentation_of_surjective,
      `FirstOrder.Language.IsolatedPresentation.exists_countable_strict_stage_bound] do
    unless chain.contains n do throwError "[CONSUMER CHAIN] the cone misses {n}"
  let (cmods, cnames) := scottViolations env chain
  let karp := cmods.filter fun (_, m) ↦ (`InfinitaryLogic.Karp).isPrefixOf m
  if karp.isEmpty || cnames.isEmpty then
    throwError "[VACUOUS CHECK] the wrapper check does not flag the consumer chain"

/-- **Axioms**: every export and every guard declaration uses only the standard axioms. -/
def checkAxioms : Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  for n in genericRoots ++ qrankRoots ++ wrapperRoots ++ guardDecls do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"

end ScottSeparationGuard

open ScottSeparationGuard in
run_cmd do
  checkClosures
  checkPlacement
  checkCones
  checkAxioms
  logInfo "Scott-separation regression guard: OK (positive: two-point exclusion, satisfiable \
    hypotheses outside the point, rank zero, independent universes, the empty space, the stage \
    omega_1 excluded, the loss-plus-survivor adapter at theta + 1, a Z-indexed and a Type 1 \
    instance of the general bound, nonvacuity on the countable ordinals; consequences: the \
    leaving form, uncountability forced, cardinality aleph_1 with countable complements; \
    negative: singleton domain, uniformity, isolation, antitonicity, the strict rank endpoint, \
    the bound not attained; semantic: countable rank, the wrapper, the consumer call shape and \
    the per-class shape through isolatedPresentation_of_surjective; exact closures of \
    OrdinalCountability, Lomega1omega.QuantifierRank and Descriptive.ScottDefinability; generic \
    cones logic-free and wrapper cones Scott-free, with positive controls; placement; standard \
    axioms)"
