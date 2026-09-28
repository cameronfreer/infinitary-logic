/-
Regression guard for the generic countable-ordinal and Cantor helpers
(`InfinitaryLogic/OrdinalCountability.lean`).

Checked: **Cantor uncountability** applied; the **rank criterion** in both directions as conditional
API composition; **countable complements from losses** as conditional composition, and the
**necessity of the limit hypothesis** on a concrete family (`D β = univ` below `ω`, `∅` from `ω`
on, over Cantor space: no successor loss, yet `(D ω)ᶜ` is uncountable); the **`ℵ₁` exhaustion
theorem** as conditional composition, and the **necessity of both extra hypotheses** on concrete
families over `Unit` (constant `univ`: countable complements but no point leaves; `univ` at `0`
and `∅` afterwards: countable complements and every point leaves, but `D 1` is empty).  Headline
declarations use only the standard axioms.

Run with: lake env lean scripts/check_ordinal_countability_regressions.lean
-/
import InfinitaryLogic.OrdinalCountability

open Lean InfinitaryLogic Cardinal Ordinal Set

/-- **Cantor uncountability** applied. -/
theorem cantor_regression : ¬ (Set.univ : Set (ℕ → Bool)).Countable := not_countable_univ_cantor

/-- **The rank criterion**, both directions. -/
theorem rank_regression {X : Type} (r : X → Ordinal.{0}) (hr : ∀ x, r x < Ordinal.omega 1)
    (hfib : ∀ α < Ordinal.omega 1, Countable {x // r x = α}) (S : Set X) :
    (S.Countable → ∃ β < Ordinal.omega 1, ∀ x ∈ S, r x < β) ∧
    ((∃ β < Ordinal.omega 1, ∀ x ∈ S, r x < β) → S.Countable) :=
  ⟨(countable_iff_rank_bounded r hr hfib S).mp, (countable_iff_rank_bounded r hr hfib S).mpr⟩

/-- **Countable complements from losses**, conditional composition. -/
theorem loss_regression {X : Type} (D : Ordinal.{0} → Set X) (h0 : D 0 = Set.univ)
    (hsucc : ∀ ξ, ξ < Ordinal.omega 1 → (D ξ \ D (ξ + 1)).Countable)
    (hlim : ∀ l, Order.IsSuccLimit l → l < Ordinal.omega 1 → (⋂ ξ < l, D ξ) ⊆ D l) :
    ∀ β, β < Ordinal.omega 1 → (D β)ᶜ.Countable :=
  compl_countable_of_loss D h0 hsucc hlim

/-- The family with no successor loss whose complement jumps at `ω`. -/
noncomputable def jumpAtOmega (β : Ordinal.{0}) : Set (ℕ → Bool) :=
  if β < Ordinal.omega0 then Set.univ else ∅

/-- **The limit hypothesis is necessary**: `jumpAtOmega` starts at `univ`, has no successor loss
below `ω₁`, and yet `(jumpAtOmega ω)ᶜ` is uncountable. -/
theorem limit_necessary_regression :
    jumpAtOmega 0 = Set.univ ∧
    (∀ ξ, ξ < Ordinal.omega 1 → (jumpAtOmega ξ \ jumpAtOmega (ξ + 1)).Countable) ∧
    ¬ (jumpAtOmega Ordinal.omega0)ᶜ.Countable := by
  refine ⟨by simp [jumpAtOmega, Ordinal.omega0_pos], fun ξ _ => ?_, ?_⟩
  · by_cases h : ξ + 1 < Ordinal.omega0
    · have h' : ξ < Ordinal.omega0 := lt_trans (Order.lt_succ ξ) (by simpa using h)
      simp [jumpAtOmega, h, h']
    · have h' : ¬ ξ < Ordinal.omega0 := fun hξ => h (by
        rw [← Order.succ_eq_add_one]; exact (Ordinal.isSuccLimit_omega0).succ_lt hξ)
      simp [jumpAtOmega, h, h']
  · simp only [jumpAtOmega, lt_self_iff_false, ite_false, Set.compl_empty]
    exact not_countable_univ_cantor

/-- **The `ℵ₁` exhaustion theorem**, conditional composition. -/
theorem exhaustion_regression {X : Type} (D : Ordinal.{0} → Set X) (hanti : Antitone D)
    (hcompl : ∀ β, β < Ordinal.omega 1 → (D β)ᶜ.Countable)
    (hne : ∀ β, β < Ordinal.omega 1 → (D β).Nonempty)
    (hleave : ∀ x, ∃ β, β < Ordinal.omega 1 ∧ x ∉ D β) :
    Cardinal.mk X = Cardinal.aleph 1 :=
  mk_eq_aleph_one_of_domains D hanti hcompl hne hleave

/-- **Both extra hypotheses are necessary.**  On `Unit`, the constant family `univ` has countable
complements and is nonempty, but no point leaves, and `#Unit ≠ ℵ₁`; the family `univ` at `0` and `∅`
afterwards has countable complements and every point leaves, but `D 1` is empty. -/
theorem hypotheses_necessary_regression :
    ((∀ β, β < Ordinal.omega 1 → ((fun _ : Ordinal.{0} => (Set.univ : Set Unit)) β)ᶜ.Countable) ∧
      ¬ (∀ x : Unit, ∃ β, β < Ordinal.omega 1 ∧ x ∉ (fun _ : Ordinal.{0} => (Set.univ : Set Unit)) β) ∧
      Cardinal.mk Unit ≠ Cardinal.aleph 1) ∧
    ((∀ β, β < Ordinal.omega 1 →
        ((fun β : Ordinal.{0} => if β = 0 then (Set.univ : Set Unit) else ∅) β)ᶜ.Countable) ∧
      (∀ x : Unit, ∃ β, β < Ordinal.omega 1 ∧
        x ∉ (fun β : Ordinal.{0} => if β = 0 then (Set.univ : Set Unit) else ∅) β) ∧
      ¬ ((fun β : Ordinal.{0} => if β = 0 then (Set.univ : Set Unit) else ∅) 1).Nonempty) := by
  refine ⟨⟨fun _ _ => by simp, fun h => ?_, ?_⟩, ⟨fun _ _ => Set.to_countable _, fun _ => ?_, ?_⟩⟩
  · obtain ⟨_, _, hx⟩ := h ()
    exact hx (Set.mem_univ _)
  · rw [Cardinal.mk_unit]
    exact fun h => absurd (h ▸ Cardinal.aleph0_lt_aleph_one : (1 : Cardinal) > Cardinal.aleph0)
      (not_lt.mpr Cardinal.one_le_aleph0)
  · refine ⟨1, ?_, by simp⟩
    rw [Cardinal.lt_omega_iff_card_lt, Ordinal.card_one]
    exact Cardinal.one_lt_aleph0.trans Cardinal.aleph0_lt_aleph_one
  · simp

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`InfinitaryLogic.not_countable_univ_cantor, `InfinitaryLogic.iSup_lt_omega1_of_forall_lt,
   `InfinitaryLogic.countable_iff_rank_bounded, `InfinitaryLogic.compl_countable_of_loss,
   `InfinitaryLogic.mk_eq_aleph_one_of_domains,
   `cantor_regression, `rank_regression, `loss_regression, `limit_necessary_regression,
   `exhaustion_regression, `hypotheses_necessary_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "ordinal-countability regression guard: OK (Cantor uncountability, rank criterion both \
    ways, countable complements from losses with the limit hypothesis shown necessary, aleph-one \
    exhaustion with both extra hypotheses shown necessary; headline declarations on standard axioms)"
