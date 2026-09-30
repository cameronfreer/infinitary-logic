/-
Regression guard for Scott processes (`InfinitaryLogic/ScottProcess/FreeArray.lean` and
`InfinitaryLogic/ScottProcess/Basic.lean`).

Checked: the **laws of the free array** (Larson, Scott processes, Definitions 2.4, 2.6, 2.11,
Proposition 2.15, Remarks 2.8, 2.13, 2.14) as headline declarations; **Example 2.17 at level 0**
for the language with a `0`-ary `S` and a binary `R` (the count `2^(n²+1)` of `Ψ^n_0`, so `32`
for `n = 2`, and the horizontal projections `H^1_0(ψ^1_0) = H^1_0(φ^1_0) = S`,
`H^2_0(ψ^2_0, i_1) = ψ^1_0`, `H^2_0(φ^2_0, {(x_0, x_1)}) = φ^1_0`); **Example 2.17 at level 1**
through `succEquiv` (`E(ψ^0_1) = {ψ^1_0}`, `E(φ^0_1) = {ψ^1_0, φ^1_0}`,
`V_{0,1}(ψ^1_1) = V_{0,1}(φ^1_1) = ψ^1_0`, `E(ψ^1_1) = {ψ^2_0}`, `E(φ^1_1) = {φ^2_0}`,
`H^1_1(ψ^1_1, i_0) = ψ^0_1`, `H^1_1(φ^1_1, i_0) = φ^0_1`); **Proposition 3.5** and
**Proposition 4.4** on the toy process `unitProcess`.  Headline declarations use only the
standard axioms.

Run with: lake env lean scripts/check_scott_process_regressions.lean
-/
import InfinitaryLogic.ScottProcess.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring

open Lean InfinitaryLogic InfinitaryLogic.ScottProcess.FreeArray

noncomputable section

/-! ### Example 2.17 at level 0 -/

/-- The relation symbols of Example 2.17: a `0`-ary `S` and a binary `R`. -/
inductive ExRel : ℕ → Type
  /-- The `0`-ary relation symbol. -/
  | S : ExRel 0
  /-- The binary relation symbol. -/
  | R : ExRel 2

/-- The relational language of Example 2.17. -/
abbrev exLang : FirstOrder.Language.{0, 0} := ⟨fun _ ↦ Empty, ExRel⟩

/-- The level-`0` data of Example 2.17. -/
abbrev ExA : AtomicData.{0} := relAtomic exLang

/-- Relation instances on `Fin n`: `S`, or `R` on an ordered pair of variables. -/
def atomEquiv (n : ℕ) : AtomInst exLang n ≃ Unit ⊕ (Fin 2 → Fin n) where
  toFun
    | ⟨_, .S, _⟩ => .inl ()
    | ⟨_, .R, f⟩ => .inr f
  invFun
    | .inl _ => ⟨0, .S, Fin.elim0⟩
    | .inr f => ⟨2, .R, f⟩
  left_inv
    | ⟨_, .S, f⟩ => by
      have : f = Fin.elim0 := funext fun i ↦ i.elim0
      subst this
      rfl
    | ⟨_, .R, _⟩ => rfl
  right_inv
    | .inl () => rfl
    | .inr _ => rfl

/-- **Example 2.17, the count**: `Ψ^n_0` has `2^(n²+1)` elements. -/
theorem card_Ψ_zero (n : ℕ) : Nat.card (Ψ ExA 0 n) = 2 ^ (n ^ 2 + 1) := by
  rw [Nat.card_congr ((zeroEquiv ExA n).trans (Equiv.ulift.trans
    (Equiv.arrowCongr (atomEquiv n) (Equiv.refl Bool))))]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_sum, Fintype.card_unit,
    Fintype.card_fin, Fintype.card_bool]
  ring_nf

/-- **Example 2.17**: `Ψ^2_0` has `32` elements. -/
theorem card_Ψ_zero_two : Nat.card (Ψ ExA 0 2) = 32 := card_Ψ_zero 2

/-- A level-`0` element from a truth assignment to the relation instances. -/
def mk0 {n : ℕ} (t : AtomInst exLang n → Bool) : Ψ ExA 0 n := (zeroEquiv ExA n).symm ⟨t⟩

/-- Unfolding `mk0`. -/
theorem zeroEquiv_mk0 {n : ℕ} (t : AtomInst exLang n → Bool) :
    zeroEquiv ExA n (mk0 t) = ⟨t⟩ :=
  Equiv.apply_symm_apply _ _

/-- `H^n_0` on `mk0` relabels the truth assignment. -/
theorem mk0_H {n m : ℕ} (j : Fin m ↪ Fin n) (t : AtomInst exLang n → Bool) :
    H j (mk0 t) = mk0 fun a ↦ t (a.map j) := by
  apply (zeroEquiv ExA m).injective
  rw [H_zero_eq_restrict, zeroEquiv_mk0, zeroEquiv_mk0]
  rfl

/-- The sentence `S`. -/
def sTrue : Ψ ExA 0 0 := mk0 fun _ ↦ true

/-- `ψ^1_0 = S ∧ R(x_0, x_0)`. -/
def ψ10' : Ψ ExA 0 1 := mk0 fun _ ↦ true

/-- `φ^1_0 = S ∧ ¬R(x_0, x_0)`. -/
def φ10' : Ψ ExA 0 1 := mk0 fun
  | ⟨_, .S, _⟩ => true
  | ⟨_, .R, _⟩ => false

/-- `ψ^2_0`: `S`, and `R(x_a, x_b)` iff `a = b`. -/
def ψ20' : Ψ ExA 0 2 := mk0 fun
  | ⟨_, .S, _⟩ => true
  | ⟨_, .R, f⟩ => decide (f 0 = f 1)

/-- `φ^2_0`: `S`, and `R(x_a, x_b)` iff `a = b = 0`. -/
def φ20' : Ψ ExA 0 2 := mk0 fun
  | ⟨_, .S, _⟩ => true
  | ⟨_, .R, f⟩ => decide (f 0 = 0 ∧ f 1 = 0)

/-- The inclusion `i_0 ∈ I_{0,1}`. -/
abbrev i01 : Fin 0 ↪ Fin 1 := Fin.castLEEmb (Nat.zero_le 1)

/-- **Example 2.17**: `H^1_0(ψ^1_0) = H^1_0(φ^1_0) = S`. -/
theorem H_level0_sentence : H i01 ψ10' = sTrue ∧ H i01 φ10' = sTrue := by
  refine ⟨?_, ?_⟩
  · rw [ψ10', mk0_H, sTrue]
  · rw [φ10', mk0_H, sTrue]
    congr 1
    funext ⟨_, r, f⟩
    cases r <;> first | rfl | exact (f 0).elim0

/-- **Example 2.17**: `H^2_0(ψ^2_0, i_1) = ψ^1_0`. -/
theorem H_level0_psi : H (Fin.castLEEmb (by decide : 1 ≤ 2)) ψ20' = ψ10' := by
  rw [ψ20', mk0_H, ψ10']
  congr 1
  funext ⟨_, r, f⟩
  cases r
  · rfl
  · exact decide_eq_true (congrArg (Fin.castLE (by decide : 1 ≤ 2)) (Subsingleton.elim (f 0) (f 1)))

/-- The injection `{(x_0, x_1)} ∈ I_{1,2}`. -/
def j01 : Fin 1 ↪ Fin 2 := ⟨fun _ ↦ 1, fun a b _ ↦ Subsingleton.elim a b⟩

/-- **Example 2.17**: `H^2_0(φ^2_0, {(x_0, x_1)}) = φ^1_0`. -/
theorem H_level0_phi : H j01 φ20' = φ10' := by
  rw [φ20', mk0_H, φ10']
  congr 1
  funext ⟨_, r, f⟩
  cases r
  · rfl
  · rfl

/-- The two level-`0` formulas `ψ^1_0` and `φ^1_0` are distinct. -/
theorem ψ10'_ne_φ10' : ψ10' ≠ φ10' := by
  intro h
  have := congrArg (fun x ↦ (zeroEquiv ExA 1 x).down ⟨2, .R, fun _ ↦ 0⟩) h
  simp only [ψ10', φ10', zeroEquiv_mk0] at this
  exact Bool.noConfusion this

/-! ### Example 2.17 at level 1 -/

/-- A successor-row element from its first component and extension set. -/
def mk1 {α : Ordinal.{0}} {n : ℕ} (φ' : Ψ ExA α n) (E' : Set (Ψ ExA α (n + 1)))
    (hE : E'.Nonempty) : Ψ ExA (α + 1) n :=
  (succEquiv ExA α n).symm (φ', ⟨E', hE⟩)

/-- `V_{α,α+1}` of `mk1` is its first component. -/
theorem V_mk1 {α : Ordinal.{0}} {n : ℕ} (φ' : Ψ ExA α n) (E' : Set (Ψ ExA α (n + 1)))
    (hE : E'.Nonempty) : V (lt_add_one α).le (mk1 φ' E' hE) = φ' := by
  rw [V_succ_eq_fst, mk1, Equiv.apply_symm_apply]

/-- `E` of `mk1` is its extension set. -/
theorem E_mk1 {α : Ordinal.{0}} {n : ℕ} (φ' : Ψ ExA α n) (E' : Set (Ψ ExA α (n + 1)))
    (hE : E'.Nonempty) : E (mk1 φ' E' hE) = E' := by
  rw [E_eq_snd, mk1, Equiv.apply_symm_apply]

/-- `H` on `mk1`, by Definition 2.11(3). -/
theorem H_mk1 {α : Ordinal.{0}} {n m : ℕ} (j : Fin m ↪ Fin n) (φ' : Ψ ExA α n)
    (E' : Set (Ψ ExA α (n + 1))) (hE : E'.Nonempty) :
    H j (mk1 φ' E' hE) =
      mk1 (H j φ') (Set.image2 (fun ψ j' ↦ H j' ψ) E' (extSet j))
        (hE.image2 ⟨_, extLast_mem j⟩) := by
  apply (succEquiv ExA α m).injective
  rw [succEquiv_H]
  simp only [mk1, Equiv.apply_symm_apply]
  rfl

/-- Congruence for `mk1`. -/
theorem mk1_congr {α : Ordinal.{0}} {n : ℕ} {φ' φ'' : Ψ ExA α n} {E' E'' : Set (Ψ ExA α (n + 1))}
    (hE' : E'.Nonempty) (hE'' : E''.Nonempty) (h1 : φ' = φ'') (h2 : E' = E'') :
    mk1 φ' E' hE' = mk1 φ'' E'' hE'' := by
  subst h1 h2
  rfl

/-- `ψ^0_1 = S ∧ ∃x_0 ψ^1_0 ∧ ∀x_0 ψ^1_0`. -/
def ψ01' : Ψ ExA (0 + 1) 0 := mk1 sTrue {ψ10'} (Set.singleton_nonempty _)

/-- `φ^0_1 = S ∧ ∃x_0 ψ^1_0 ∧ ∃x_0 φ^1_0 ∧ ∀x_0 (ψ^1_0 ∨ φ^1_0)`. -/
def φ01' : Ψ ExA (0 + 1) 0 := mk1 sTrue {ψ10', φ10'} (Set.insert_nonempty _ _)

/-- `ψ^1_1 = ψ^1_0 ∧ ∃x_1 ψ^2_0 ∧ ∀x_1 (x_1 ≠ x_0 → ψ^2_0)`. -/
def ψ11' : Ψ ExA (0 + 1) 1 := mk1 ψ10' {ψ20'} (Set.singleton_nonempty _)

/-- `φ^1_1 = ψ^1_0 ∧ ∃x_1 φ^2_0 ∧ ∀x_1 (x_1 ≠ x_0 → φ^2_0)`. -/
def φ11' : Ψ ExA (0 + 1) 1 := mk1 ψ10' {φ20'} (Set.singleton_nonempty _)

/-- **Example 2.17 at level 1**: the extension sets and vertical projections. -/
theorem level1_E_V :
    E ψ01' = {ψ10'} ∧ E φ01' = {ψ10', φ10'} ∧ E ψ11' = {ψ20'} ∧ E φ11' = {φ20'} ∧
      V (lt_add_one 0).le ψ11' = ψ10' ∧ V (lt_add_one 0).le φ11' = ψ10' :=
  ⟨E_mk1 .., E_mk1 .., E_mk1 .., E_mk1 .., V_mk1 .., V_mk1 ..⟩

/-- Every `H^2_0(ψ^2_0, j')` for `j' ∈ I_{1,2}` is `ψ^1_0`. -/
theorem H_ψ20' (j' : Fin 1 ↪ Fin 2) : H j' ψ20' = ψ10' := by
  rw [ψ20', mk0_H, ψ10']
  congr 1
  funext ⟨_, r, f⟩
  cases r
  · rfl
  · exact decide_eq_true (congrArg (⇑j') (Subsingleton.elim (f 0) (f 1)))

/-- **Example 2.17**: `H^1_1(ψ^1_1, i_0) = ψ^0_1`. -/
theorem H_level1_psi : H i01 ψ11' = ψ01' := by
  rw [ψ11', H_mk1, ψ01']
  refine mk1_congr _ _ H_level0_sentence.1 ?_
  rw [Set.image2_singleton_left]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨extLast i01, extLast_mem i01, H_ψ20' _⟩, ?_⟩
  rintro _ ⟨j', -, rfl⟩
  exact H_ψ20' j'

/-- `H^2_0(φ^2_0, j')` is `ψ^1_0` when `j'` sends `x_0` to `x_0`. -/
theorem H_φ20'_of_zero (j' : Fin 1 ↪ Fin 2) (h : j' 0 = 0) : H j' φ20' = ψ10' := by
  rw [φ20', mk0_H, ψ10']
  congr 1
  funext ⟨_, r, f⟩
  cases r
  · rfl
  · show decide (j' (f 0) = 0 ∧ j' (f 1) = 0) = true
    rw [Subsingleton.elim (f 0) 0, Subsingleton.elim (f 1) 0, h]
    decide

/-- `H^2_0(φ^2_0, j')` is `φ^1_0` when `j'` sends `x_0` to `x_1`. -/
theorem H_φ20'_of_one (j' : Fin 1 ↪ Fin 2) (h : j' 0 = 1) : H j' φ20' = φ10' := by
  rw [φ20', mk0_H, φ10']
  congr 1
  funext ⟨_, r, f⟩
  cases r
  · rfl
  · show decide (j' (f 0) = 0 ∧ j' (f 1) = 0) = false
    rw [Subsingleton.elim (f 0) 0, Subsingleton.elim (f 1) 0, h]
    decide

/-- **Example 2.17**: `H^1_1(φ^1_1, i_0) = φ^0_1`. -/
theorem H_level1_phi : H i01 φ11' = φ01' := by
  rw [φ11', H_mk1, φ01']
  refine mk1_congr _ _ H_level0_sentence.1 ?_
  rw [Set.image2_singleton_left]
  ext x
  constructor
  · rintro ⟨j', -, rfl⟩
    rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (j' 0) with h | h
    · exact Or.inl (H_φ20'_of_zero j' h)
    · exact Or.inr (H_φ20'_of_one j' h)
  · rintro (rfl | rfl)
    · exact ⟨extTo i01 0 fun i ↦ i.elim0, extTo_mem _ _ _, H_φ20'_of_zero _ rfl⟩
    · exact ⟨extLast i01, extLast_mem _, H_φ20'_of_one _ rfl⟩

end

/-! ### The toy process -/

/-- **Proposition 3.5 on the toy process**: the one-row process has a unique sentence. -/
theorem unitProcess_sentence :
    ∃! φ, φ ∈ (ScottProcess.unitProcess.{0} 1 zero_lt_one).Φ 0 zero_lt_one 0 :=
  (ScottProcess.unitProcess 1 zero_lt_one).existsUnique_mem_zero 0 zero_lt_one

/-- **Proposition 4.4 on the toy process** of length `2`, at `α = 0 < β = 1`. -/
theorem unitProcess_E_V_eq (n : ℕ) (φ : Ψ ScottProcess.unitData.{0} 1 n) :
    E (V (Order.add_one_le_of_lt zero_lt_one) φ) =
      V zero_lt_one.le '' {ψ ∈ (ScottProcess.unitProcess.{0} 2 two_pos).Φ 1 one_lt_two (n + 1) |
        H (Fin.castLEEmb (Nat.le_succ n)) ψ = φ} :=
  (ScottProcess.unitProcess 2 two_pos).E_V_eq zero_lt_one one_lt_two (Set.mem_univ φ)

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`InfinitaryLogic.ScottProcess.FreeArray.level, `InfinitaryLogic.ScottProcess.FreeArray.V,
   `InfinitaryLogic.ScottProcess.FreeArray.E, `InfinitaryLogic.ScottProcess.FreeArray.H,
   `InfinitaryLogic.ScottProcess.FreeArray.V_succ_eq_fst,
   `InfinitaryLogic.ScottProcess.FreeArray.E_eq_snd,
   `InfinitaryLogic.ScottProcess.FreeArray.V_limit_eq_entry,
   `InfinitaryLogic.ScottProcess.FreeArray.H_zero_eq_restrict,
   `InfinitaryLogic.ScottProcess.FreeArray.H_zero_rel,
   `InfinitaryLogic.ScottProcess.FreeArray.V_H_comm, `InfinitaryLogic.ScottProcess.FreeArray.E_H,
   `InfinitaryLogic.ScottProcess.FreeArray.V_comp, `InfinitaryLogic.ScottProcess.FreeArray.H_comp,
   `InfinitaryLogic.ScottProcess.FreeArray.H_id,
   `InfinitaryLogic.ScottProcess.FreeArray.H_limit_entry,
   `InfinitaryLogic.ScottProcess.FreeArray.exists_succ_of_V_E,
   `InfinitaryLogic.ScottProcess.FreeArray.exists_limit_of_thread,
   `InfinitaryLogic.ScottProcess.image_H_eq, `InfinitaryLogic.ScottProcess.existsUnique_mem_zero,
   `InfinitaryLogic.ScottProcess.E_eq_of_mem_zero,
   `InfinitaryLogic.ScottProcess.image_V_fiber_subset, `InfinitaryLogic.ScottProcess.biUnion_E_eq,
   `InfinitaryLogic.ScottProcess.E_V_add_one_eq, `InfinitaryLogic.ScottProcess.E_V_eq,
   `InfinitaryLogic.ScottProcess.unitProcess,
   `card_Ψ_zero, `card_Ψ_zero_two, `H_level0_sentence, `H_level0_psi, `H_level0_phi,
   `ψ10'_ne_φ10', `level1_E_V, `H_level1_psi, `H_level1_phi, `unitProcess_sentence,
   `unitProcess_E_V_eq]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "scott-process regression guard: OK (free-array laws; Example 2.17 at level 0 and \
    level 1; Proposition 3.5 and Proposition 4.4 on the toy process; headline declarations on \
    standard axioms)"
