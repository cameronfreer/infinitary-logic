/-
Regression guard for Scott processes (`InfinitaryLogic/ScottProcess/FreeArray.lean` and
`InfinitaryLogic/ScottProcess/Basic.lean`).

Every law below is *applied* to a concrete term, not only listed for its axioms.

* **Example 2.17 at level 0**, for the language with a `0`-ary `S` and a binary `R`, over
  `relAtomic`: the count `2^(n²+1)` of `Ψ^n_0` (so `32` for `n = 2`), and, through `H_zero_rel`,
  the horizontal projections `H^1_0(ψ^1_0) = H^1_0(φ^1_0) = S`, `H^2_0(ψ^2_0, i_1) = ψ^1_0`,
  `H^2_0(φ^2_0, {(x_0, x_1)}) = φ^1_0`.
* **Example 2.17 at level 1**, built with `mkSucc` and compared with `Ψ.ext_succ`:
  `E(ψ^0_1) = {ψ^1_0}`, `E(φ^0_1) = {ψ^1_0, φ^1_0}`, `V_{0,1}(ψ^1_1) = V_{0,1}(φ^1_1) = ψ^1_0`,
  `E(ψ^1_1) = {ψ^2_0}`, `E(φ^1_1) = {φ^2_0}`, `H^1_1(ψ^1_1, i_0) = ψ^0_1`,
  `H^1_1(φ^1_1, i_0) = φ^0_1` (`E_mkSucc`, `V_mkSucc`, `H_mkSucc`).
* **The array laws on Example 2.17**: `V_H_comm` (Proposition 2.15), `E_H` (Definition
  2.11(3)), `H_comp` (Remark 2.14(2)), `H_id` (Remark 2.13), `exists_succ_of_V_E`; and the
  `simp` normal forms `H_id`, `H_comp`, `V_comp`.
* **Row `ω`** over the one-point data: a family through the finite rows is realized at row `ω`
  by `exists_limit_of_thread` (condition (b) is vacuous below `ω`, by
  `Ordinal.omega0_le_of_isSuccLimit`), and read back with `V_limit_eq_entry`, `H_limit_entry`,
  `V_comp` and `Ψ.ext_limit`.
* **Scott processes** on the toy processes `unitProcess`: Proposition 3.5
  (`existsUnique_mem_zero`), Remark 3.4 (`image_H_eq`), the remark after Proposition 3.5
  (`E_eq_of_mem_zero`), Propositions 4.1–4.4 (`image_V_fiber_subset`, `biUnion_E_eq`,
  `E_V_add_one_eq`, `E_V_eq`), and `ScottProcess.ext`: every process over the one-point data
  is `unitProcess`.

The headline declarations use only the standard axioms.

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
    | ⟨.rel .S _, _⟩ => .inl ()
    | ⟨.rel .R f, _⟩ => .inr f
    | ⟨.eq _ _, h⟩ => h.elim
  invFun
    | .inl _ => ⟨.rel .S Fin.elim0, trivial⟩
    | .inr f => ⟨.rel .R f, trivial⟩
  left_inv
    | ⟨.rel .S f, _⟩ => by
      have : f = Fin.elim0 := funext fun i ↦ i.elim0
      subst this
      rfl
    | ⟨.rel .R _, _⟩ => rfl
    | ⟨.eq _ _, h⟩ => h.elim
  right_inv
    | .inl () => rfl
    | .inr _ => rfl

/-- `atomEquiv` is natural in the variables. -/
theorem atomEquiv_map {n m : ℕ} (f : Fin m → Fin n) (a : AtomInst exLang m) :
    atomEquiv n (a.map f) = Sum.map id (f ∘ ·) (atomEquiv m a) := by
  obtain ⟨_ | ⟨r, g⟩, h⟩ := a
  · exact h.elim
  · cases r <;> rfl

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

/-- `H^n_0` on `mk0` relabels the truth assignment (by `H_zero_rel`). -/
theorem mk0_H {n m : ℕ} (j : Fin m ↪ Fin n) (t : AtomInst exLang n → Bool) :
    H j (mk0 t) = mk0 fun a ↦ t (a.map j) := by
  apply (zeroEquiv ExA m).injective
  rw [zeroEquiv_mk0]
  refine ULift.ext (funext fun a ↦ ?_)
  rw [H_zero_rel, zeroEquiv_mk0]

/-- A level-`0` element from the truth value `s` of `S` and the truth values `r` of `R`. -/
def mkA {n : ℕ} (s : Bool) (r : (Fin 2 → Fin n) → Bool) : Ψ ExA 0 n :=
  mk0 fun a ↦ Sum.elim (fun _ ↦ s) r (atomEquiv n a)

/-- `H^n_0` on `mkA` relabels the arguments of `R`. -/
theorem mkA_H {n m : ℕ} (j : Fin m ↪ Fin n) (s : Bool) (r : (Fin 2 → Fin n) → Bool) :
    H j (mkA s r) = mkA s fun f ↦ r (j ∘ f) := by
  rw [mkA, mk0_H, mkA]
  congr 1
  funext a
  rw [atomEquiv_map]
  cases atomEquiv m a <;> rfl

/-- The sentence `S`. -/
def sTrue : Ψ ExA 0 0 := mkA true fun _ ↦ true

/-- `ψ^1_0 = S ∧ R(x_0, x_0)`. -/
def ψ10' : Ψ ExA 0 1 := mkA true fun _ ↦ true

/-- `φ^1_0 = S ∧ ¬R(x_0, x_0)`. -/
def φ10' : Ψ ExA 0 1 := mkA true fun _ ↦ false

/-- `ψ^2_0`: `S`, and `R(x_a, x_b)` iff `a = b`. -/
def ψ20' : Ψ ExA 0 2 := mkA true fun f ↦ decide (f 0 = f 1)

/-- `φ^2_0`: `S`, and `R(x_a, x_b)` iff `a = b = 0`. -/
def φ20' : Ψ ExA 0 2 := mkA true fun f ↦ decide (f 0 = 0 ∧ f 1 = 0)

/-- The inclusion `i_0 ∈ I_{0,1}`. -/
abbrev i01 : Fin 0 ↪ Fin 1 := Fin.castLEEmb (Nat.zero_le 1)

/-- **Example 2.17**: `H^1_0(ψ^1_0) = H^1_0(φ^1_0) = S`. -/
theorem H_level0_sentence : H i01 ψ10' = sTrue ∧ H i01 φ10' = sTrue := by
  refine ⟨?_, ?_⟩
  · rw [ψ10', mkA_H, sTrue]
  · rw [φ10', mkA_H, sTrue]
    congr 1
    funext f
    exact (f 0).elim0

/-- **Example 2.17**: `H^2_0(ψ^2_0, i_1) = ψ^1_0`. -/
theorem H_level0_psi : H (Fin.castLEEmb (by decide : 1 ≤ 2)) ψ20' = ψ10' := by
  rw [ψ20', mkA_H, ψ10']
  congr 1
  funext f
  exact decide_eq_true (congrArg (Fin.castLE (by decide : 1 ≤ 2)) (Subsingleton.elim (f 0) (f 1)))

/-- The injection `{(x_0, x_1)} ∈ I_{1,2}`. -/
def j01 : Fin 1 ↪ Fin 2 := ⟨fun _ ↦ 1, fun a b _ ↦ Subsingleton.elim a b⟩

/-- **Example 2.17**: `H^2_0(φ^2_0, {(x_0, x_1)}) = φ^1_0`. -/
theorem H_level0_phi : H j01 φ20' = φ10' := by
  rw [φ20', mkA_H, φ10']
  rfl

/-- The two level-`0` formulas `ψ^1_0` and `φ^1_0` are distinct. -/
theorem ψ10'_ne_φ10' : ψ10' ≠ φ10' := by
  intro h
  have := congrArg (fun x ↦ (zeroEquiv ExA 1 x).down ⟨.rel .R fun _ ↦ 0, trivial⟩) h
  simp only [ψ10', φ10', mkA, zeroEquiv_mk0] at this
  exact Bool.noConfusion this

/-- **Remark 2.14(2) on Example 2.17** (`H_comp`):
`H^2_0(φ^2_0, {(x_0, x_1)} ∘ i_0) = H^1_0(φ^1_0) = S`. -/
theorem H_comp_level0 : H (i01.trans j01) φ20' = sTrue := by
  rw [← H_comp, H_level0_phi, H_level0_sentence.2]

/-! ### Example 2.17 at level 1 -/

/-- `ψ^0_1 = S ∧ ∃x_0 ψ^1_0 ∧ ∀x_0 ψ^1_0`. -/
def ψ01' : Ψ ExA (0 + 1) 0 := mkSucc sTrue {ψ10'} (Set.singleton_nonempty _)

/-- `φ^0_1 = S ∧ ∃x_0 ψ^1_0 ∧ ∃x_0 φ^1_0 ∧ ∀x_0 (ψ^1_0 ∨ φ^1_0)`. -/
def φ01' : Ψ ExA (0 + 1) 0 := mkSucc sTrue {ψ10', φ10'} (Set.insert_nonempty _ _)

/-- `ψ^1_1 = ψ^1_0 ∧ ∃x_1 ψ^2_0 ∧ ∀x_1 (x_1 ≠ x_0 → ψ^2_0)`. -/
def ψ11' : Ψ ExA (0 + 1) 1 := mkSucc ψ10' {ψ20'} (Set.singleton_nonempty _)

/-- `φ^1_1 = ψ^1_0 ∧ ∃x_1 φ^2_0 ∧ ∀x_1 (x_1 ≠ x_0 → φ^2_0)`. -/
def φ11' : Ψ ExA (0 + 1) 1 := mkSucc ψ10' {φ20'} (Set.singleton_nonempty _)

/-- **Example 2.17 at level 1**: the extension sets and vertical projections. -/
theorem level1_E_V :
    E ψ01' = {ψ10'} ∧ E φ01' = {ψ10', φ10'} ∧ E ψ11' = {ψ20'} ∧ E φ11' = {φ20'} ∧
      V (lt_add_one 0).le ψ11' = ψ10' ∧ V (lt_add_one 0).le φ11' = ψ10' :=
  ⟨E_mkSucc .., E_mkSucc .., E_mkSucc .., E_mkSucc .., V_mkSucc .., V_mkSucc ..⟩

/-- Every `H^2_0(ψ^2_0, j')` for `j' ∈ I_{1,2}` is `ψ^1_0`. -/
theorem H_ψ20' (j' : Fin 1 ↪ Fin 2) : H j' ψ20' = ψ10' := by
  rw [ψ20', mkA_H, ψ10']
  congr 1
  funext f
  exact decide_eq_true (congrArg (⇑j') (Subsingleton.elim (f 0) (f 1)))

/-- **Example 2.17**: `H^1_1(ψ^1_1, i_0) = ψ^0_1`. -/
theorem H_level1_psi : H i01 ψ11' = ψ01' := by
  rw [ψ11', H_mkSucc, ψ01']
  refine Ψ.ext_succ ?_ ?_
  · rw [V_mkSucc, V_mkSucc, H_level0_sentence.1]
  rw [E_mkSucc, E_mkSucc, Set.image2_singleton_left]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨extLast i01, extLast_mem i01, H_ψ20' _⟩, ?_⟩
  rintro _ ⟨j', -, rfl⟩
  exact H_ψ20' j'

/-- `H^2_0(φ^2_0, j')` is `ψ^1_0` when `j'` sends `x_0` to `x_0`. -/
theorem H_φ20'_of_zero (j' : Fin 1 ↪ Fin 2) (h : j' 0 = 0) : H j' φ20' = ψ10' := by
  rw [φ20', mkA_H, ψ10']
  congr 1
  funext f
  simp [Subsingleton.elim (f 0) 0, Subsingleton.elim (f 1) 0, h]

/-- `H^2_0(φ^2_0, j')` is `φ^1_0` when `j'` sends `x_0` to `x_1`. -/
theorem H_φ20'_of_one (j' : Fin 1 ↪ Fin 2) (h : j' 0 = 1) : H j' φ20' = φ10' := by
  rw [φ20', mkA_H, φ10']
  congr 1
  funext f
  simp [Subsingleton.elim (f 0) 0, Subsingleton.elim (f 1) 0, h]

/-- **Example 2.17**: `H^1_1(φ^1_1, i_0) = φ^0_1`. -/
theorem H_level1_phi : H i01 φ11' = φ01' := by
  rw [φ11', H_mkSucc, φ01']
  refine Ψ.ext_succ ?_ ?_
  · rw [V_mkSucc, V_mkSucc, H_level0_sentence.1]
  rw [E_mkSucc, E_mkSucc, Set.image2_singleton_left]
  ext x
  constructor
  · rintro ⟨j', -, rfl⟩
    rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (j' 0) with h | h
    · exact Or.inl (H_φ20'_of_zero j' h)
    · exact Or.inr (H_φ20'_of_one j' h)
  · rintro (rfl | rfl)
    · exact ⟨extTo i01 0 fun i ↦ i.elim0, extTo_mem _ _ _, H_φ20'_of_zero _ rfl⟩
    · exact ⟨extLast i01, extLast_mem _, H_φ20'_of_one _ rfl⟩

/-! ### The array laws on Example 2.17 -/

/-- **Proposition 2.15 on Example 2.17** (`V_H_comm`): `V_{0,1}(H^1_1(φ^1_1, i_0)) = S`. -/
theorem V_H_level1 : V (lt_add_one 0).le (H i01 φ11') = sTrue := by
  rw [V_H_comm, level1_E_V.2.2.2.2.2, H_level0_sentence.1]

/-- **Definition 2.11(3) on Example 2.17** (`E_H`):
`E(H^1_1(φ^1_1, i_0)) = H[{φ^2_0} × extSet i_0]`. -/
theorem E_H_level1 :
    E (H i01 φ11') = Set.image2 (fun ψ j' ↦ H j' ψ) {φ20'} (extSet i01) := by
  rw [E_H, level1_E_V.2.2.2.1]

/-- **Remark 2.13 on Example 2.17** (`H_id`): `H^1_1(φ^1_1, id) = φ^1_1`. -/
theorem H_id_level1 : H (Function.Embedding.refl (Fin 1)) φ11' = φ11' :=
  H_id φ11'

/-- **Fullness on Example 2.17** (`exists_succ_of_V_E`): `(ψ^1_0, {ψ^2_0, φ^2_0})` is realized
at row `1`, and differs from `ψ^1_1`. -/
theorem exists_succ_level1 :
    ∃ φ : Ψ ExA (0 + 1) 1, V (lt_add_one 0).le φ = ψ10' ∧ E φ = {ψ20', φ20'} ∧ φ ≠ ψ11' := by
  obtain ⟨φ, hV, hE⟩ := exists_succ_of_V_E ψ10' {ψ20', φ20'} (Set.insert_nonempty _ _)
  refine ⟨φ, hV, hE, fun h ↦ ?_⟩
  have h2 : φ20' ∈ E ψ11' := by rw [← h, hE]; exact Or.inr rfl
  rw [level1_E_V.2.2.1, Set.mem_singleton_iff] at h2
  have := congrArg (H j01) h2
  rw [H_level0_phi, H_ψ20'] at this
  exact ψ10'_ne_φ10' this.symm

/-- **`simp` normal forms**: `simp` closes `H_id`, `H_comp` and `V_comp` goals, and a goal
combining them, without looping. -/
theorem simp_normal_forms {α β δ : Ordinal.{0}} (hδ : δ ≤ β) (hβ : β ≤ α) {n m l : ℕ}
    (j : Fin m ↪ Fin n) (k : Fin l ↪ Fin m) (x : Ψ ExA α n) :
    H (Function.Embedding.refl _) x = x ∧ H k (H j x) = H (k.trans j) x ∧
      V hδ (V hβ x) = V (hδ.trans hβ) x ∧
      V hδ (V hβ (H k (H j x))) = V (hδ.trans hβ) (H (k.trans j) x) := by
  simp

/-! ### Row `ω` -/

/-- `2 < ω`. -/
theorem two_lt_ω : (2 : Ordinal.{0}) < Ordinal.omega0 := by
  simpa using Ordinal.natCast_lt_omega0 2

/-- **Row `ω`** (`exists_limit_of_thread`): over the one-point data, every family through the
finite rows satisfying (a) is realized at row `ω`; condition (b) is vacuous, since no row below
`ω` is a limit. -/
theorem row_omega_realized (n : ℕ) (ψ : ∀ β < Ordinal.omega0, Ψ ScottProcess.unitData.{0} β n) :
    ∃ φ : Ψ ScottProcess.unitData.{0} Ordinal.omega0 n, ∀ β (h : β < Ordinal.omega0),
      V h.le φ = ψ β h :=
  exists_limit_of_thread Ordinal.isSuccLimit_omega0 ψ (fun _ _ ↦ Subsingleton.elim _ _)
    fun _ h hβ ↦ absurd h (not_lt.2 (Ordinal.omega0_le_of_isSuccLimit hβ))

/-- **Row `ω`, read back** (`V_limit_eq_entry`, `H_limit_entry`, `V_comp`): the element
realizing a family has that family as its thread; `H` acts on its entries; and its projection
to row `1` factors through row `2`. -/
theorem row_omega_readback (n : ℕ) (j : Fin n ↪ Fin n)
    (ψ : ∀ β < Ordinal.omega0, Ψ ScottProcess.unitData.{0} β n) :
    ∃ φ : Ψ ScottProcess.unitData.{0} Ordinal.omega0 n,
      (limEquiv _ Ordinal.isSuccLimit_omega0 n φ).1 2 two_lt_ω = ψ 2 two_lt_ω ∧
      (limEquiv _ Ordinal.isSuccLimit_omega0 n (H j φ)).1 2 two_lt_ω = H j (ψ 2 two_lt_ω) ∧
      V one_le_two (V two_lt_ω.le φ) = V (one_le_two.trans two_lt_ω.le) φ := by
  obtain ⟨φ, hφ⟩ := row_omega_realized n ψ
  refine ⟨φ, ?_, ?_, V_comp _ _ φ⟩
  · rw [← V_limit_eq_entry Ordinal.isSuccLimit_omega0 two_lt_ω, hφ]
  · rw [H_limit_entry Ordinal.isSuccLimit_omega0 two_lt_ω,
      ← V_limit_eq_entry Ordinal.isSuccLimit_omega0 two_lt_ω, hφ]

/-- **Row `ω`, extensionality** (`Ψ.ext_limit`): elements of row `ω` over the one-point data
agree. -/
theorem row_omega_ext (n : ℕ) (φ ψ : Ψ ScottProcess.unitData.{0} Ordinal.omega0 n) : φ = ψ :=
  Ψ.ext_limit Ordinal.isSuccLimit_omega0 fun _ _ ↦ Subsingleton.elim _ _

end

/-! ### The toy processes -/

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

/-- `1 < ω`. -/
theorem one_lt_ω : (1 : Ordinal.{0}) < Ordinal.omega0 := Ordinal.one_lt_omega0

/-- `0 + 1 < ω`. -/
theorem zero_add_one_lt_ω : (0 : Ordinal.{0}) + 1 < Ordinal.omega0 := by
  rw [zero_add]; exact one_lt_ω

/-- `1 + 1 < ω`. -/
theorem one_add_one_lt_ω : (1 : Ordinal.{0}) + 1 < Ordinal.omega0 := by
  rw [one_add_one_eq_two]; exact two_lt_ω

/-- The toy process of length `ω`. -/
abbrev Pω : ScottProcess ScottProcess.unitData.{0} Ordinal.omega0 :=
  ScottProcess.unitProcess Ordinal.omega0 Ordinal.omega0_pos

/-- **Remark 3.4 on the toy process** (`image_H_eq`): `Φ^1_1 = H[Φ^3_1 × {j}]`. -/
theorem unitProcess_image_H (j : Fin 1 ↪ Fin 3) :
    Pω.Φ 1 one_lt_ω 1 = H j '' Pω.Φ 1 one_lt_ω 3 :=
  Pω.image_H_eq 1 one_lt_ω j

/-- **The remark after Proposition 3.5 on the toy process** (`E_eq_of_mem_zero`). -/
theorem unitProcess_E_eq_of_mem_zero (φ : Ψ ScottProcess.unitData.{0} (0 + 1) 0) :
    E φ = Pω.Φ 0 ((lt_add_one 0).trans zero_add_one_lt_ω) 1 :=
  Pω.E_eq_of_mem_zero 0 zero_add_one_lt_ω (Set.mem_univ φ)

/-- **Proposition 4.1 on the toy process** (`image_V_fiber_subset`). -/
theorem unitProcess_image_V_fiber (j : Fin 1 ↪ Fin 2) (φ : Ψ ScottProcess.unitData.{0} 1 1) :
    V zero_le_one '' {ψ ∈ Pω.Φ 1 one_lt_ω 2 | H j ψ = φ} ⊆
      {θ ∈ Pω.Φ 0 (zero_le_one.trans_lt one_lt_ω) 2 | H j θ = V zero_le_one φ} :=
  Pω.image_V_fiber_subset zero_le_one one_lt_ω j φ

/-- **Proposition 4.2 on the toy process** (`biUnion_E_eq`). -/
theorem unitProcess_biUnion_E (φ : Ψ ScottProcess.unitData.{0} 0 1) :
    ⋃ ψ ∈ {ψ ∈ Pω.Φ (0 + 1) zero_add_one_lt_ω 1 | V (lt_add_one 0).le ψ = φ}, E ψ =
      {θ ∈ Pω.Φ 0 ((lt_add_one 0).trans zero_add_one_lt_ω) 2 |
        H (Fin.castLEEmb (Nat.le_succ 1)) θ = φ} :=
  Pω.biUnion_E_eq 0 zero_add_one_lt_ω φ

/-- **Proposition 4.3 on the toy process** (`E_V_add_one_eq`), at `α = 0 ≤ β = 1`. -/
theorem unitProcess_E_V_add_one (φ : Ψ ScottProcess.unitData.{0} (1 + 1) 1) :
    E (V (Order.add_one_le_of_lt (Order.lt_add_one_iff.2 zero_le_one)) φ) =
      V zero_le_one '' E φ :=
  Pω.E_V_add_one_eq zero_le_one one_add_one_lt_ω (Set.mem_univ φ)

/-- **`ScottProcess.ext` on the one-point data**: every Scott process over `unitData` is
`unitProcess`, since each column of each level is nonempty (Proposition 3.5 and Remark 3.4) and
every column is a singleton. -/
theorem eq_unitProcess {δ : Ordinal.{0}} (P : ScottProcess ScottProcess.unitData.{0} δ) :
    P = ScottProcess.unitProcess δ P.pos := by
  ext α hα n x
  simp only [ScottProcess.unitProcess_Φ, Set.mem_univ, iff_true]
  obtain ⟨φ, hφ⟩ := P.nonempty_zero α hα
  rw [P.image_H_eq α hα (Fin.castLEEmb (Nat.zero_le n))] at hφ
  obtain ⟨ψ, hψ, -⟩ := hφ
  rwa [Subsingleton.elim x ψ]

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`InfinitaryLogic.ScottProcess.FreeArray.level, `InfinitaryLogic.ScottProcess.FreeArray.V,
   `InfinitaryLogic.ScottProcess.FreeArray.E, `InfinitaryLogic.ScottProcess.FreeArray.H,
   `InfinitaryLogic.ScottProcess.FreeArray.extTo, `InfinitaryLogic.ScottProcess.FreeArray.relAtomic,
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
   `InfinitaryLogic.ScottProcess.FreeArray.mkSucc,
   `InfinitaryLogic.ScottProcess.FreeArray.V_mkSucc,
   `InfinitaryLogic.ScottProcess.FreeArray.E_mkSucc,
   `InfinitaryLogic.ScottProcess.FreeArray.H_mkSucc,
   `InfinitaryLogic.ScottProcess.FreeArray.Ψ.ext_succ,
   `InfinitaryLogic.ScottProcess.FreeArray.Ψ.ext_limit,
   `InfinitaryLogic.ScottProcess.ext,
   `InfinitaryLogic.ScottProcess.image_H_eq, `InfinitaryLogic.ScottProcess.existsUnique_mem_zero,
   `InfinitaryLogic.ScottProcess.E_eq_of_mem_zero,
   `InfinitaryLogic.ScottProcess.image_V_fiber_subset, `InfinitaryLogic.ScottProcess.biUnion_E_eq,
   `InfinitaryLogic.ScottProcess.E_V_add_one_eq, `InfinitaryLogic.ScottProcess.E_V_eq,
   `InfinitaryLogic.ScottProcess.unitProcess,
   `card_Ψ_zero, `card_Ψ_zero_two, `mk0_H, `H_level0_sentence, `H_level0_psi, `H_level0_phi,
   `ψ10'_ne_φ10', `H_comp_level0, `level1_E_V, `H_level1_psi, `H_level1_phi, `V_H_level1,
   `E_H_level1, `H_id_level1, `exists_succ_level1, `simp_normal_forms, `row_omega_realized,
   `row_omega_readback, `row_omega_ext, `unitProcess_sentence, `unitProcess_E_V_eq,
   `unitProcess_image_H, `unitProcess_E_eq_of_mem_zero, `unitProcess_image_V_fiber,
   `unitProcess_biUnion_E, `unitProcess_E_V_add_one, `eq_unitProcess]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "scott-process regression guard: OK (applied: Example 2.17 at level 0 via H_zero_rel \
    and at level 1 via mkSucc, V_mkSucc, E_mkSucc, H_mkSucc and Ψ.ext_succ; V_H_comm, E_H, \
    H_comp, H_id and exists_succ_of_V_E on Example 2.17; simp normal forms H_id, H_comp, V_comp; \
    row ω via exists_limit_of_thread, V_limit_eq_entry, H_limit_entry, V_comp and Ψ.ext_limit; \
    Proposition 3.5, Remark 3.4, the remark after Proposition 3.5, Propositions 4.1-4.4 and \
    ScottProcess.ext on the toy processes; headline declarations on standard axioms)"
