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

Four construction-free lemmas requested by a consumer of the descriptive theory, placed here
because they mention no logic.  `ω₁` is `Ordinal.omega 1` throughout, as in `OrdinalUtil`
(`Cardinal.ord_aleph` converts from `(aleph 1).ord`).  Mathlib is reused wherever it already has
the fact; nothing here adds an instance.

* `countable_iff_rank_bounded`: for a rank into the countable ordinals with countable fibres, a
  set is countable iff its ranks are bounded below `ω₁`.  Forward: enumerate the set and bound the
  supremum by regularity of `ℵ₁`; backward: a countable union of countable fibres over a countable
  initial segment (`setCountable_Iio_of_lt_omega1`).
* `compl_countable_of_loss`: countable successor losses and a limit-continuity hypothesis give
  countable complements below `ω₁`, by transfinite induction.  The limit hypothesis is explicit and
  necessary; no monotonicity is assumed.
* `mk_eq_aleph_one_of_domains`: antitone domains with countable complements, nonempty below `ω₁`,
  and left by every point, exhaust a type of cardinality exactly `ℵ₁`, stated universe-polymorphically
  (`aleph 1` in the universe of `X`; `Cardinal.lift_aleph` relates the universes).
* `not_countable_univ_cantor`: Cantor space is uncountable, from `#(ℕ → Bool) = 𝔠` and `ℵ₀ < 𝔠`.
-/

universe u

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

/-! ### Rank and countability -/

variable {X : Type u}

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
    have hsub : S ⊆ ⋃ α ∈ Set.Iio β, {x | r x = α} := fun x hx =>
      Set.mem_iUnion₂.mpr ⟨r x, hS x hx, rfl⟩
    refine (Set.Countable.biUnion (setCountable_Iio_of_lt_omega1 β hβ) fun α hα => ?_).mono hsub
    exact Set.countable_coe_iff.mp (hfib α (lt_trans hα hβ))

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

/-- **Domains exhaust a type of cardinality `ℵ₁`.**  Antitone domains with countable complements,
nonempty below `ω₁`, and left by every point.  Both extra hypotheses are needed: `D β = univ` on
`Unit` has countable complements and no point leaves; `D 0 = univ`, `D β = ∅` for `β ≥ 1` has countable
complements and every point leaves, but `D 1` is empty. -/
theorem mk_eq_aleph_one_of_domains (D : Ordinal.{0} → Set X) (hanti : Antitone D)
    (hcompl : ∀ β, β < Ordinal.omega 1 → (D β)ᶜ.Countable)
    (hne : ∀ β, β < Ordinal.omega 1 → (D β).Nonempty)
    (hleave : ∀ x, ∃ β, β < Ordinal.omega 1 ∧ x ∉ D β) :
    Cardinal.mk X = Cardinal.aleph 1 := by
  classical
  choose β hβ hxβ using hleave
  apply le_antisymm
  · -- upper bound: inject into the sigma of the countable complements over the countable ordinals
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
  · -- lower bound: uncountable, since a countable enumeration would leave every domain
    rw [Cardinal.aleph_one_le_iff, ← not_le, Cardinal.mk_le_aleph0_iff]
    intro hX
    have : Nonempty X := (hne 0 (Ordinal.omega_pos 1)).elim fun x _ => ⟨x⟩
    obtain ⟨g, hg⟩ := exists_surjective_nat X
    have hs : (⨆ n, β (g n)) < Ordinal.omega 1 :=
      iSup_lt_omega1_of_forall_lt _ fun n => hβ (g n)
    obtain ⟨x, hx⟩ := hne _ hs
    obtain ⟨n, rfl⟩ := hg x
    exact hxβ (g n) (hanti (Ordinal.le_iSup (fun n => β (g n)) n) hx)

end InfinitaryLogic
