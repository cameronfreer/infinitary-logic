/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.OrdinalUtil
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Generic countable-ordinal and Cantor helpers

Construction-free lemmas about ranks into the countable ordinals, requested by consumers of the
descriptive theory and placed here because they mention no logic.  `ω₁` is `Ordinal.omega 1`
throughout, as in `OrdinalUtil` (`Cardinal.ord_aleph` converts from `(aleph 1).ord`).  Mathlib is
reused wherever it already has the fact; nothing here adds an instance.

## Sections

* **Cantor space.**  `not_countable_univ_cantor`: Cantor space is uncountable, from
  `#(ℕ → Bool) = 𝔠` and `ℵ₀ < 𝔠`.
* **Suprema.**  `iSup_lt_omega1_of_forall_lt`: a sequence of countable ordinals has a countable
  supremum (regularity of `ℵ₁`).  `iSup_add_one_lt_omega1`: over any countable index type, the
  supremum of the successors of countable ordinals is countable.
* **Rank and countability.**  `countable_iff_rank_bounded`: for a rank `r` with `r x < ω₁` and
  countable fibers below `ω₁`, a set is countable iff its ranks are bounded below `ω₁`.  Forward:
  enumerate the set and bound the supremum by regularity of `ℵ₁`; backward
  (`countable_of_forall_rank_lt`, which needs only the countable fibers): a countable union of
  countable fibers over a countable initial segment (`setCountable_Iio_of_lt_omega1`).
* **Countable complements from losses.**  `compl_countable_of_loss`: countable successor losses and
  a limit-continuity hypothesis give countable complements below `ω₁`, by transfinite induction.
  The limit hypothesis is explicit and necessary; no monotonicity is assumed.
* **Exhaustion by domains.**  `mk_le_aleph_one_of_domains`: domains with countable complements
  below `ω₁`, left by every point, bound `#X` by `ℵ₁` (no monotonicity, no nonemptiness).
  `mk_eq_aleph_one_of_domains`: antitone such domains that are moreover nonempty below `ω₁` give
  `#X = ℵ₁`.  Both are universe-polymorphic (`aleph 1` in the universe of `X`;
  `Cardinal.lift_aleph` relates the universes).
* **Separation by an isolating observation.**  For an abstract satisfaction relation
  `Sat : F → X → Prop`: `notMem_of_isolating_of_uniform`, a point isolated by `φ` lies in no
  nonsingleton set on which `φ` is constant; `lt_index_of_isolating_of_antitone` (any linear
  order of stages), for antitone domains that are nonsingleton and agree on `φ` at an index `ζ`,
  every stage containing the point lies strictly below `ζ`, with the rank form
  `lt_rank_of_isolating_of_antitone` (`ζ := rank φ`) and its `Ordinal.{0}` form
  `stage_lt_rank_of_isolating`; `exists_countable_strict_stage_bound_of_isolation`, isolating
  observations of countable rank and rank-uniform nonsingleton domains below `ω₁` bound every
  point's stages by a countable ordinal.  See the section for the conventions.
* **Rank tails.**  `rankTail r η = {x | η ≤ r x}`, with the simp lemma `mem_rankTail` and the
  bridge `rankTail_eq_preimage_Ici`.  Unconditionally: `rankTail_zero`, `rankTail_antitone`,
  `compl_rankTail`, `notMem_rankTail_succ` (a point leaves the tail just above its rank),
  `rankTail_diff_succ` (the successor loss at `η` is the fiber at `η`) and
  `rankTail_eq_iInter_of_isSuccPrelimit` (continuity at every successor-prelimit, `0` included;
  `rankTail_eq_iInter_of_isSuccLimit` at limits).  Under `r x < ω₁` for all `x` and countable
  fibers below `ω₁`, each lemma assuming only what it uses: countable complements below `ω₁`
  (`rankTail_compl_countable`, fibers only), countable losses (`rankTail_loss_countable`), no
  point in every tail below `ω₁` (`biInter_rankTail_eq_empty`, rank bound only), empty tails from
  `ω₁` on (`rankTail_eq_empty_of_omega1_le`, rank bound only), `#X ≤ ℵ₁`
  (`mk_le_aleph_one_of_countable_fibers`), `#X = ℵ₁` for uncountable `X`
  (`mk_eq_aleph_one_of_countable_fibers`), and nonempty losses cofinal below `ω₁` iff `X` is
  uncountable (`rankTail_cofinal_losses_iff`).
* **Least level of a cover.**  `leastLevel Q x = sInf {α | x ∈ Q α}`.  With no hypothesis on `Q`:
  `leastLevel_le_of_mem`, and `leastLevel_mem_of_exists` for a point lying in some `Q α`.  Under
  the explicit covering hypothesis `⋃ α < ω₁, Q α = univ` (without it a point in no `Q α` gets
  level `sInf ∅ = 0`): `leastLevel_mem`, `leastLevel_lt_omega1`, `setOf_leastLevel_eq_subset`,
  `countable_fibers_leastLevel` (countable members below `ω₁` give countable fibers), and
  `rankTail_leastLevel`: the tail at `η` is the complement of `⋃ α < η, Q α`.  So a cover by
  countable sets feeds the rank-tail lemmas.
-/

universe u v w

open Cardinal Ordinal Set

namespace InfinitaryLogic

/-! ### Cantor space -/

/-- **Cantor space is uncountable**, by cardinal arithmetic. -/
theorem not_countable_univ_cantor : ¬ (Set.univ : Set (ℕ → Bool)).Countable := by
  rw [Set.countable_univ_iff, ← Cardinal.mk_le_aleph0_iff]
  have hcard : Cardinal.mk (ℕ → Bool) = Cardinal.continuum := by simp
  rw [hcard]
  exact not_le.mpr Cardinal.aleph0_lt_continuum

/-! ### Suprema of countably many countable ordinals -/

/-- The supremum of a sequence of countable ordinals is countable (regularity of `ℵ₁`). -/
theorem iSup_lt_omega1_of_forall_lt (f : ℕ → Ordinal.{0}) (hf : ∀ n, f n < Ordinal.omega 1) :
    (⨆ n, f n) < Ordinal.omega 1 := by
  apply Ordinal.lift_iSup_lt_of_lt_cof _ hf
  rw [Ordinal.lift_id, ← Cardinal.ord_aleph, Cardinal.isRegular_aleph_one.cof_ord, Cardinal.lift_id,
    Cardinal.mk_nat]
  exact Cardinal.aleph0_lt_aleph_one

/-- **Countable supremum of successors**: over a countable index type, the supremum of the
successors of countable ordinals is countable. -/
theorem iSup_add_one_lt_omega1 {C : Type*} [Countable C] (α : C → Ordinal.{0})
    (hα : ∀ c, α c < Ordinal.omega 1) : (⨆ c, (α c + 1)) < Ordinal.omega 1 :=
  Ordinal.iSup_lt_omega_one fun c ↦ (Cardinal.isSuccLimit_omega 1).add_one_lt (hα c)

/-! ### Rank and countability -/

variable {X : Type u}

/-- **Bounded ranks give countability**: the backward half of `countable_iff_rank_bounded`.  It
needs only countable fibers below `ω₁`, not the bound `r x < ω₁` on every rank. -/
theorem countable_of_forall_rank_lt (r : X → Ordinal.{0})
    (hfib : ∀ α < Ordinal.omega 1, Countable {x // r x = α}) {S : Set X} {β : Ordinal.{0}}
    (hβ : β < Ordinal.omega 1) (hS : ∀ x ∈ S, r x < β) : S.Countable := by
  have hsub : S ⊆ ⋃ α ∈ Set.Iio β, {x | r x = α} := fun x hx =>
    Set.mem_iUnion₂.mpr ⟨r x, hS x hx, rfl⟩
  refine (Set.Countable.biUnion (setCountable_Iio_of_lt_omega1 β hβ) fun α hα => ?_).mono hsub
  exact Set.countable_coe_iff.mp (hfib α (lt_trans hα hβ))

/-- **Countability equals boundedness below `ω₁`** for a rank into the countable ordinals with
countable fibres. -/
theorem countable_iff_rank_bounded (r : X → Ordinal.{0}) (hr : ∀ x, r x < Ordinal.omega 1)
    (hfib : ∀ α < Ordinal.omega 1, Countable {x // r x = α}) (S : Set X) :
    S.Countable ↔ ∃ β < Ordinal.omega 1, ∀ x ∈ S, r x < β := by
  constructor
  · intro hS
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, Ordinal.omega_pos 1, fun x hx => hx.elim⟩
    · obtain ⟨g, rfl⟩ := hS.exists_eq_range hne
      have hlim : Order.IsSuccLimit (Ordinal.omega 1) := by
        rw [← Cardinal.ord_aleph]
        exact Cardinal.isSuccLimit_ord (Cardinal.aleph0_le_aleph 1)
      refine ⟨⨆ n, Order.succ (r (g n)),
        iSup_lt_omega1_of_forall_lt _ fun n => hlim.succ_lt (hr (g n)), ?_⟩
      rintro _ ⟨n, rfl⟩
      exact (Order.lt_succ (r (g n))).trans_le (Ordinal.le_iSup (fun n => Order.succ (r (g n))) n)
  · rintro ⟨β, hβ, hS⟩
    exact countable_of_forall_rank_lt r hfib hβ hS

/-! ### Countable complements from successor losses -/

/-- **Countable complements from countable successor losses and limit continuity.**  No
monotonicity of `D` is assumed; the limit hypothesis is necessary. -/
theorem compl_countable_of_loss (D : Ordinal.{0} → Set X) (h0 : D 0 = Set.univ)
    (hsucc : ∀ ξ, ξ < Ordinal.omega 1 → (D ξ \ D (ξ + 1)).Countable)
    (hlim : ∀ l, Order.IsSuccLimit l → l < Ordinal.omega 1 → (⋂ ξ < l, D ξ) ⊆ D l) :
    ∀ β, β < Ordinal.omega 1 → (D β)ᶜ.Countable := by
  intro β
  induction β using WellFoundedLT.induction with
  | _ β ih =>
    intro hβ
    rcases Ordinal.zero_or_succ_or_isSuccLimit β with rfl | ⟨ξ, rfl⟩ | hl
    · rw [h0, Set.compl_univ]
      exact Set.countable_empty
    · have hξ : ξ < Ordinal.omega 1 := lt_trans (Order.lt_succ ξ) hβ
      refine ((ih ξ (Order.lt_succ ξ) hξ).union (hsucc ξ hξ)).mono fun x hx => ?_
      rw [Order.succ_eq_add_one] at hx
      by_cases hxξ : x ∈ D ξ
      · exact Or.inr ⟨hxξ, hx⟩
      · exact Or.inl hxξ
    · refine (Set.Countable.biUnion (setCountable_Iio_of_lt_omega1 β hβ) fun ξ hξ =>
        ih ξ hξ (lt_trans hξ hβ)).mono fun x hx => ?_
      by_contra hall
      apply hx
      apply hlim β hl hβ
      refine Set.mem_iInter₂.mpr fun ξ hξ => ?_
      by_contra hxξ
      exact hall (Set.mem_iUnion₂.mpr ⟨ξ, hξ, hxξ⟩)

/-! ### Exhaustion by domains: cardinality exactly `ℵ₁` -/

/-- **Domains with countable complements bound a type by `ℵ₁`**: the upper half of
`mk_eq_aleph_one_of_domains`.  If every point leaves some `D β` with `β < ω₁` and every such
complement is countable, `X` injects into a sigma of `ℵ₁` countable sets.  Neither monotonicity
nor nonempty domains is assumed. -/
theorem mk_le_aleph_one_of_domains (D : Ordinal.{0} → Set X)
    (hcompl : ∀ β, β < Ordinal.omega 1 → (D β)ᶜ.Countable)
    (hleave : ∀ x, ∃ β, β < Ordinal.omega 1 ∧ x ∉ D β) :
    Cardinal.mk X ≤ Cardinal.aleph 1 := by
  classical
  choose β hβ hxβ using hleave
  -- inject into the sigma of the countable complements over the countable ordinals
  let ι : Type 1 := Set.Iio (Ordinal.omega 1)
  let F : ι → Type u := fun b => ↥(D b.1)ᶜ
  let e : X → Σ b : ι, F b := fun x => ⟨⟨β x, hβ x⟩, ⟨x, hxβ x⟩⟩
  have he : Function.Injective e := fun x y hxy => by
    have := congrArg (fun p : Σ b : ι, F b => (p.2.1 : X)) hxy
    exact this
  have h1 : Cardinal.lift.{max 1 u} (Cardinal.mk X) ≤
      Cardinal.lift.{u} (Cardinal.mk (Σ b : ι, F b)) :=
    Cardinal.lift_mk_le_lift_mk_of_injective he
  have h2 : Cardinal.mk (Σ b : ι, F b) ≤
      Cardinal.lift.{u} (Cardinal.mk ι) * (Cardinal.aleph0 : Cardinal.{max 1 u}) := by
    rw [Cardinal.mk_sigma]
    calc (Cardinal.sum fun b => Cardinal.mk (F b))
        ≤ Cardinal.sum fun _ : ι => (Cardinal.aleph0 : Cardinal.{u}) :=
          Cardinal.sum_le_sum _ _ fun b => by
            rw [Cardinal.mk_le_aleph0_iff]
            exact (hcompl b.1 b.2).to_subtype
      _ = Cardinal.lift.{u} (Cardinal.mk ι) * Cardinal.lift.{1} (Cardinal.aleph0 : Cardinal.{u}) :=
          Cardinal.sum_const ι _
      _ = Cardinal.lift.{u} (Cardinal.mk ι) * (Cardinal.aleph0 : Cardinal.{max 1 u}) := by
          rw [Cardinal.lift_aleph0]
  have hι : Cardinal.mk ι = Cardinal.lift.{1} (Cardinal.aleph 1 : Cardinal.{0}) := by
    rw [Cardinal.mk_Iio_ordinal, Ordinal.card_omega]
  have h3 : Cardinal.lift.{u} (Cardinal.mk ι) * (Cardinal.aleph0 : Cardinal.{max 1 u}) =
      Cardinal.lift.{max 1 u} (Cardinal.aleph 1 : Cardinal.{u}) := by
    rw [hι, Cardinal.lift_lift]
    simp only [Cardinal.lift_aleph, Ordinal.lift_one]
    exact Cardinal.mul_eq_left (Cardinal.aleph0_le_aleph 1)
      (Cardinal.aleph0_le_aleph 1) Cardinal.aleph0_ne_zero
  have := h1.trans (Cardinal.lift_le.mpr h2)
  rw [h3, Cardinal.lift_lift] at this
  exact Cardinal.lift_le.mp this

/-- **Domains exhaust a type of cardinality `ℵ₁`.**  Antitone domains with countable complements,
nonempty below `ω₁`, and left by every point.  The upper bound is `mk_le_aleph_one_of_domains`.
Both extra hypotheses are needed: `D β = univ` on `Unit` has countable complements and no point
leaves; `D 0 = univ`, `D β = ∅` for `β ≥ 1` has countable complements and every point leaves,
but `D 1` is empty. -/
theorem mk_eq_aleph_one_of_domains (D : Ordinal.{0} → Set X) (hanti : Antitone D)
    (hcompl : ∀ β, β < Ordinal.omega 1 → (D β)ᶜ.Countable)
    (hne : ∀ β, β < Ordinal.omega 1 → (D β).Nonempty)
    (hleave : ∀ x, ∃ β, β < Ordinal.omega 1 ∧ x ∉ D β) :
    Cardinal.mk X = Cardinal.aleph 1 := by
  refine le_antisymm (mk_le_aleph_one_of_domains D hcompl hleave) ?_
  classical
  choose β hβ hxβ using hleave
  -- lower bound: uncountable, since a countable enumeration would leave every domain
  rw [Cardinal.aleph_one_le_iff, ← not_le, Cardinal.mk_le_aleph0_iff]
  intro hX
  have : Nonempty X := (hne 0 (Ordinal.omega_pos 1)).elim fun x _ => ⟨x⟩
  obtain ⟨g, hg⟩ := exists_surjective_nat X
  have hs : (⨆ n, β (g n)) < Ordinal.omega 1 :=
    iSup_lt_omega1_of_forall_lt _ fun n => hβ (g n)
  obtain ⟨x, hx⟩ := hne _ hs
  obtain ⟨n, rfl⟩ := hg x
  exact hxβ (g n) (hanti (Ordinal.le_iSup (fun n => β (g n)) n) hx)

/-! ### Separation by an isolating observation

`Sat : F → X → Prop` is an abstract satisfaction relation between observations and points, and
`φ` **isolates** `q` when `∀ x, Sat φ x ↔ x = q`.  No logic, order on `X`, topology or
countability enters `notMem_of_isolating_of_uniform`, `lt_index_of_isolating_of_antitone`,
`lt_rank_of_isolating_of_antitone` or `stage_lt_rank_of_isolating`.

* **Rank convention.**  Agreement at a stage `η` is for observations of rank **at most** `η`
  (`rank φ ≤ η` in `exists_countable_strict_stage_bound_of_isolation`, as in `EquivQRω`), and the
  strict exclusion happens at the isolating observation's own rank.  Under the convention
  "agreement for ranks strictly below `η`", the bound **at** `rank φ` (the conclusion of
  `stage_lt_rank_of_isolating`) is lost: an isolating observation of rank exactly `η` need not
  agree on the domain at `η`.  A countable strict bound as in
  `exists_countable_strict_stage_bound_of_isolation` still holds there, with `θ := rank φ + 1`,
  but it needs agreement and nonsingletonness at that later stage.
* **What the bound is.**  It is the rank of a *chosen* isolating observation, so it depends on
  that choice.  It is not an internal Scott rank, and it is not an attained stage: attainment of
  a greatest stage needs further closure hypotheses and is `exists_greatest_stage_lt_omega1` in
  `OrdinalUtil`.
* **Nonsingletonness is essential.**  With `D = {q}` and `Sat φ x := x = q`, isolation and
  agreement hold but `q ∈ D`; neither nonemptiness of `D` nor `Nontrivial X` can replace
  `D.Nontrivial`.
* **No countability of exceptional classes** (complements, losses or fibers of the domains) is
  assumed anywhere.
* **Vacuity on countable spaces.**  The hypotheses of
  `exists_countable_strict_stage_bound_of_isolation` imply that `X` is uncountable (countably
  many countable bounds have a countable supremum, and the domain there is nonempty), so it
  applies to a countable `X` only vacuously; the other two statements are not vacuous on finite
  spaces.
* **Exhaustion.**  Under antitonicity, `∀ η, q ∈ D η → η < θ` is equivalent to `q ∉ D θ`, so the
  conclusion of `exists_countable_strict_stage_bound_of_isolation` is the "every point leaves"
  premise of `mk_le_aleph_one_of_domains` and `mk_eq_aleph_one_of_domains`.

The application with `Sat` the satisfaction of `Lω₁ω` sentences on a presentation of
isomorphism classes, isolated by Scott sentences, and `rank` the quantifier rank, is
`IsolatedPresentation.exists_countable_strict_stage_bound` in `Descriptive/ScottDefinability`;
Scott theory enters there, through the isolation hypothesis only.

The separation bounds were offered for upstreaming by a consumer of this library. -/

section Separation

variable {F : Type v}

/-- **An isolated point is outside every nonsingleton set on which its isolating observation is
constant.**  If `q ∈ D`, every member of `D` satisfies `φ`, as `q` does, hence equals `q`; this
contradicts `D.Nontrivial`.  Mere nonemptiness of `D` does not suffice (`D = {q}`). -/
theorem notMem_of_isolating_of_uniform (Sat : F → X → Prop) {D : Set X} {q : X} {φ : F}
    (hiso : ∀ x, Sat φ x ↔ x = q)
    (huniform : ∀ ⦃x y⦄, x ∈ D → y ∈ D → (Sat φ x ↔ Sat φ y))
    (htwo : D.Nontrivial) :
    q ∉ D := fun hq ↦
  let ⟨x, hx, y, hy, hxy⟩ := htwo
  hxy (((hiso x).mp ((huniform hq hx).mp ((hiso q).mpr rfl))).trans
    ((hiso y).mp ((huniform hq hy).mp ((hiso q).mpr rfl))).symm)

/-- **Strict stage bound at an index, over any linear order of stages.**  For antitone domains
`D` such that `D ζ` is nonsingleton and agrees on an observation `φ` isolating `q`, every stage
containing `q` lies strictly below `ζ`: otherwise antitonicity puts `q` in `D ζ`, contradicting
`notMem_of_isolating_of_uniform`.  Agreement is needed only for `φ` and only at `ζ`; nothing is
assumed about `η`. -/
theorem lt_index_of_isolating_of_antitone {ι : Type w} [LinearOrder ι] (Sat : F → X → Prop)
    (D : ι → Set X) (hanti : Antitone D) {q : X} {φ : F} {ζ : ι}
    (hiso : ∀ x, Sat φ x ↔ x = q)
    (huniform : ∀ ⦃x y⦄, x ∈ D ζ → y ∈ D ζ → (Sat φ x ↔ Sat φ y))
    (htwo : (D ζ).Nontrivial) {η : ι} (hq : q ∈ D η) :
    η < ζ :=
  lt_of_not_ge fun hle ↦ notMem_of_isolating_of_uniform Sat hiso huniform htwo (hanti hle hq)

/-- **Strict stage bound at the rank of an isolating observation**, over any linear order of
stages: `lt_index_of_isolating_of_antitone` at `ζ := rank φ`.  Agreement is needed only for `φ`
and only at `rank φ`; nothing is assumed about `η`. -/
theorem lt_rank_of_isolating_of_antitone {ι : Type w} [LinearOrder ι] (Sat : F → X → Prop)
    (rank : F → ι) (D : ι → Set X) (hanti : Antitone D) {q : X} {φ : F}
    (hiso : ∀ x, Sat φ x ↔ x = q)
    (huniform : ∀ ⦃x y⦄, x ∈ D (rank φ) → y ∈ D (rank φ) → (Sat φ x ↔ Sat φ y))
    (htwo : (D (rank φ)).Nontrivial) {η : ι} (hq : q ∈ D η) :
    η < rank φ :=
  lt_index_of_isolating_of_antitone Sat D hanti hiso huniform htwo hq

/-- **Strict stage bound for one isolating observation**, with `Ordinal.{0}` stages: the instance
of `lt_rank_of_isolating_of_antitone`.  No countability of `η` or of `rank φ`, and no positivity
of `rank φ`, is assumed: at rank `0` the point lies in no domain. -/
theorem stage_lt_rank_of_isolating (Sat : F → X → Prop) (rank : F → Ordinal.{0})
    (D : Ordinal.{0} → Set X) (hanti : Antitone D) {q : X} {φ : F}
    (hiso : ∀ x, Sat φ x ↔ x = q)
    (huniform : ∀ ⦃x y⦄, x ∈ D (rank φ) → y ∈ D (rank φ) → (Sat φ x ↔ Sat φ y))
    (htwo : (D (rank φ)).Nontrivial) {η : Ordinal.{0}} (hq : q ∈ D η) :
    η < rank φ :=
  lt_rank_of_isolating_of_antitone Sat rank D hanti hiso huniform htwo hq

/-- **Countable strict stage bounds from isolation.**  If every point has an isolating
observation of countable rank, and the antitone domains are nonsingleton and agree on every
observation of rank at most `η` at every countable `η`, then every point `q` has a countable
`θ` (the rank of an isolating observation chosen for `q`) bounding strictly **every** stage
containing `q`, countable or not.  The hypotheses force `X` to be uncountable (see the section
notes). -/
theorem exists_countable_strict_stage_bound_of_isolation (Sat : F → X → Prop)
    (rank : F → Ordinal.{0}) (D : Ordinal.{0} → Set X) (hanti : Antitone D)
    (huniform : ∀ η, η < Ordinal.omega 1 → ∀ φ, rank φ ≤ η →
      ∀ ⦃x y⦄, x ∈ D η → y ∈ D η → (Sat φ x ↔ Sat φ y))
    (htwo : ∀ η, η < Ordinal.omega 1 → (D η).Nontrivial)
    (hisolate : ∀ q, ∃ φ, rank φ < Ordinal.omega 1 ∧ ∀ x, Sat φ x ↔ x = q) (q : X) :
    ∃ θ, θ < Ordinal.omega 1 ∧ ∀ η, q ∈ D η → η < θ :=
  let ⟨φ, hφ, hiso⟩ := hisolate q
  ⟨rank φ, hφ, fun _ hq ↦ stage_lt_rank_of_isolating Sat rank D hanti hiso
    (huniform _ hφ φ le_rfl) (htwo _ hφ) hq⟩

end Separation

/-! ### Rank tails -/

/-- The **tails** of a rank: `rankTail r η = {x | η ≤ r x}`, the points of rank at least `η`. -/
def rankTail (r : X → Ordinal.{0}) (η : Ordinal.{0}) : Set X := {x | η ≤ r x}

/-- Membership in a rank tail: `x ∈ rankTail r η` iff `η ≤ r x`. -/
@[simp]
theorem mem_rankTail {r : X → Ordinal.{0}} {η : Ordinal.{0}} {x : X} :
    x ∈ rankTail r η ↔ η ≤ r x :=
  Iff.rfl

/-- A tail is the preimage of a closed upper ray, the bridge to Mathlib's `Ici` API. -/
theorem rankTail_eq_preimage_Ici (r : X → Ordinal.{0}) (η : Ordinal.{0}) :
    rankTail r η = r ⁻¹' Set.Ici η :=
  rfl

section RankTail

variable (r : X → Ordinal.{0})

/-- Every point has rank at least `0`. -/
@[simp]
theorem rankTail_zero : rankTail r 0 = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ mem_rankTail.2 zero_le

/-- The tails decrease. -/
theorem rankTail_antitone : Antitone (rankTail r) := fun _ _ h _ hx ↦ h.trans hx

/-- The complement of a tail is a strict initial segment of ranks. -/
@[simp]
theorem compl_rankTail (η : Ordinal.{0}) : (rankTail r η)ᶜ = {x | r x < η} := by
  ext x; simp

/-- A point leaves the tail just above its own rank. -/
theorem notMem_rankTail_succ (x : X) : x ∉ rankTail r (Order.succ (r x)) :=
  fun h ↦ (Order.lt_succ (r x)).not_ge (mem_rankTail.1 h)

/-- The **successor loss** at `η` is exactly the fiber of the rank at `η`. -/
theorem rankTail_diff_succ (η : Ordinal.{0}) :
    rankTail r η \ rankTail r (Order.succ η) = {x | r x = η} := by
  ext x
  simp only [mem_sdiff, mem_rankTail, mem_ofPred_eq, Order.succ_le_iff, not_lt]
  exact ⟨fun h ↦ le_antisymm h.2 h.1, fun h ↦ ⟨h.ge, h.le⟩⟩

/-- **Continuity at prelimits**: the tail at a successor-prelimit `l` is the intersection of the
earlier tails.  This includes `l = 0`, where both sides are `univ`. -/
theorem rankTail_eq_iInter_of_isSuccPrelimit {l : Ordinal.{0}} (hl : Order.IsSuccPrelimit l) :
    rankTail r l = ⋂ η < l, rankTail r η := by
  ext x
  simp only [mem_rankTail, mem_iInter]
  refine ⟨fun h η hη ↦ hη.le.trans h, fun h ↦ not_lt.mp fun hlt ↦ ?_⟩
  exact notMem_rankTail_succ r x (h _ (hl.succ_lt hlt))

/-- **Continuity at limits**, the limit case of `rankTail_eq_iInter_of_isSuccPrelimit`. -/
theorem rankTail_eq_iInter_of_isSuccLimit {l : Ordinal.{0}} (hl : Order.IsSuccLimit l) :
    rankTail r l = ⋂ η < l, rankTail r η :=
  rankTail_eq_iInter_of_isSuccPrelimit r hl.isSuccPrelimit

variable (hr : ∀ x, r x < Ordinal.omega 1)
    (hfib : ∀ α < Ordinal.omega 1, Countable {x // r x = α})
include hr hfib

omit hr in
/-- With countable fibers below `ω₁`, the complement of a tail below `ω₁` is countable. -/
theorem rankTail_compl_countable {η : Ordinal.{0}} (hη : η < Ordinal.omega 1) :
    (rankTail r η)ᶜ.Countable :=
  countable_of_forall_rank_lt r hfib hη fun x hx ↦ by simpa using hx

/-- Every successor loss is countable: a fiber below `ω₁`, and empty from `ω₁` on. -/
theorem rankTail_loss_countable (η : Ordinal.{0}) :
    (rankTail r η \ rankTail r (Order.succ η)).Countable := by
  rw [rankTail_diff_succ]
  by_cases hη : η < Ordinal.omega 1
  · exact Set.countable_coe_iff.mp (hfib η hη)
  · refine Set.Subsingleton.countable fun x hx ↦ ?_
    exact absurd (Set.mem_ofPred.1 hx ▸ hr x) hη

omit hfib in
/-- **No persistent core**: no point lies in every tail below `ω₁`. -/
theorem biInter_rankTail_eq_empty : (⋂ η < Ordinal.omega 1, rankTail r η) = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦ notMem_rankTail_succ r x
    (Set.mem_iInter₂.mp hx _ ((Cardinal.isSuccLimit_omega 1).succ_lt (hr x)))

omit hfib in
/-- The tails are empty from `ω₁` on. -/
theorem rankTail_eq_empty_of_omega1_le {η : Ordinal.{0}} (h : Ordinal.omega 1 ≤ η) :
    rankTail r η = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦ (hr x).not_ge (h.trans (mem_rankTail.1 hx))

/-- A rank into the countable ordinals with countable fibers bounds the type by `ℵ₁`, through
`mk_le_aleph_one_of_domains` on the tails. -/
theorem mk_le_aleph_one_of_countable_fibers : Cardinal.mk X ≤ Cardinal.aleph 1 :=
  mk_le_aleph_one_of_domains (rankTail r) (fun _ hβ ↦ rankTail_compl_countable r hfib hβ)
    fun x ↦ ⟨Order.succ (r x), (Cardinal.isSuccLimit_omega 1).succ_lt (hr x),
      notMem_rankTail_succ r x⟩

/-- An uncountable type with such a rank has cardinality exactly `ℵ₁`. -/
theorem mk_eq_aleph_one_of_countable_fibers (hX : ¬ Countable X) :
    Cardinal.mk X = Cardinal.aleph 1 := by
  refine le_antisymm (mk_le_aleph_one_of_countable_fibers r hr hfib) ?_
  rw [Cardinal.aleph_one_le_iff, ← not_le, Cardinal.mk_le_aleph0_iff]
  exact hX

/-- **Cofinal losses**: nonempty successor losses occur cofinally below `ω₁` iff `X` is
uncountable, by `countable_iff_rank_bounded` on `univ`. -/
theorem rankTail_cofinal_losses_iff :
    (∀ γ < Ordinal.omega 1, ∃ η, γ ≤ η ∧ η < Ordinal.omega 1 ∧
      (rankTail r η \ rankTail r (Order.succ η)).Nonempty) ↔ ¬ Countable X := by
  have hrb := countable_iff_rank_bounded r hr hfib Set.univ
  rw [Set.countable_univ_iff] at hrb
  refine ⟨fun h hX ↦ ?_, fun hX γ hγ ↦ ?_⟩
  · obtain ⟨β, hβ, hb⟩ := hrb.mp hX
    obtain ⟨η, hβη, -, x, hx⟩ := h β hβ
    rw [rankTail_diff_succ] at hx
    exact (hb x (mem_univ x)).not_ge (hβη.trans_eq (Set.mem_ofPred.1 hx).symm)
  · by_contra hno
    refine hX (hrb.mpr ⟨γ, hγ, fun x _ ↦ not_le.mp fun hγx ↦ hno ?_⟩)
    exact ⟨r x, hγx, hr x, x, by rw [rankTail_diff_succ]; rfl⟩

end RankTail

/-! ### The least level of a cover -/

section Cover

variable (Q : Ordinal.{0} → Set X)

/-- The **least level** of `x` in a family `Q`: the least `α` with `x ∈ Q α`.  It is `0` when `x`
lies in no `Q α` (`sInf ∅ = 0`), so the lemmas below assume that `Q` covers `X` below `ω₁`. -/
noncomputable def leastLevel (x : X) : Ordinal.{0} := sInf {α | x ∈ Q α}

variable {Q} in
/-- The least level is at most every level containing the point (no covering hypothesis). -/
theorem leastLevel_le_of_mem {x : X} {α : Ordinal.{0}} (h : x ∈ Q α) : leastLevel Q x ≤ α :=
  csInf_le' h

variable {Q} in
/-- A point lying in some member of the family lies in the member at its least level. -/
theorem leastLevel_mem_of_exists {x : X} (hx : ∃ α, x ∈ Q α) : x ∈ Q (leastLevel Q x) :=
  csInf_mem hx

variable (hcover : (⋃ α < Ordinal.omega 1, Q α) = Set.univ)
include hcover

/-- The covering hypothesis, pointwise. -/
private theorem exists_lt_omega1_mem_of_cover (x : X) : ∃ α < Ordinal.omega 1, x ∈ Q α :=
  let ⟨α, hα, hxα⟩ := Set.mem_iUnion₂.mp (hcover ▸ mem_univ x)
  ⟨α, hα, hxα⟩

/-- A point lies in the member of the cover at its least level. -/
theorem leastLevel_mem (x : X) : x ∈ Q (leastLevel Q x) :=
  let ⟨α, _, hα⟩ := exists_lt_omega1_mem_of_cover Q hcover x
  leastLevel_mem_of_exists ⟨α, hα⟩

/-- The least level is countable. -/
theorem leastLevel_lt_omega1 (x : X) : leastLevel Q x < Ordinal.omega 1 :=
  let ⟨_, hα, hxα⟩ := exists_lt_omega1_mem_of_cover Q hcover x
  (leastLevel_le_of_mem hxα).trans_lt hα

/-- The fiber of the least level at `α` lies in `Q α`. -/
theorem setOf_leastLevel_eq_subset (α : Ordinal.{0}) : {x | leastLevel Q x = α} ⊆ Q α := by
  rintro x rfl
  exact leastLevel_mem Q hcover x

/-- A cover by countable sets gives the least level countable fibers below `ω₁`. -/
theorem countable_fibers_leastLevel (hQ : ∀ α < Ordinal.omega 1, (Q α).Countable) :
    ∀ α < Ordinal.omega 1, Countable {x // leastLevel Q x = α} := fun α hα ↦
  ((hQ α hα).mono (setOf_leastLevel_eq_subset Q hcover α)).to_subtype

/-- The tails of the least level are the complements of the initial unions of the cover. -/
theorem rankTail_leastLevel (η : Ordinal.{0}) :
    rankTail (leastLevel Q) η = (⋃ α < η, Q α)ᶜ := by
  ext x
  simp only [mem_rankTail, mem_compl_iff, mem_iUnion, not_exists]
  refine ⟨fun h α hα hxα ↦ ?_, fun h ↦ not_lt.mp fun hlt ↦ h _ hlt (leastLevel_mem Q hcover x)⟩
  exact (h.trans (leastLevel_le_of_mem hxα)).not_gt hα

end Cover

end InfinitaryLogic
