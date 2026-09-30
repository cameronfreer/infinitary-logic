/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ScottProcess.FreeArray
import Mathlib.Data.Fintype.Sum

/-!
# Scott processes

The Scott processes of Larson, *Scott processes* (Beyond First Order Model Theory, vol. I),
Definition 3.1, over the free array `FreeArray.Ψ A` of `InfinitaryLogic.ScottProcess.FreeArray`,
together with the first consequences of the definition: Remark 3.4, Proposition 3.5, the
remark following it, and Propositions 4.1–4.4.

## Main declarations

* `ScottProcess A δ`: a sequence `⟨Φ α : α < δ⟩` of levels `Φ α n ⊆ Ψ A α n` satisfying the
  five formula conditions (1a)–(1e) and the three coherence conditions (2a)–(2c).
* `ScottProcess.image_H_eq`: Remark 3.4, `Φ^m_α = H[Φ^n_α × {j}]` for every `j : Fin m ↪ Fin n`.
* `ScottProcess.existsUnique_mem_zero`: Proposition 3.5, each `Φ^0_α` has a unique element.
* `ScottProcess.E_eq_of_mem_zero`: the remark after Proposition 3.5, `E(φ) = Φ^1_α` for the
  unique sentence `φ` of `Φ_{α+1}`.
* `ScottProcess.image_V_fiber_subset` (Proposition 4.1), `ScottProcess.biUnion_E_eq`
  (Proposition 4.2), `ScottProcess.E_V_add_one_eq` (Proposition 4.3),
  `ScottProcess.E_V_eq` (Proposition 4.4).
* `ScottProcess.unitProcess`: the process with every level full over the one-point level-`0`
  data `unitData`, of any nonzero length.

## Interpretation choices

* **Columns.** Larson's `Φ_α ⊆ Ψ_α` is a set of formulas with any number of free variables,
  and `Φ^n_α = Φ_α ∩ Ψ^n_α`.  Since `Ψ A α n` is a separate type for each `n`, a level is the
  family `n ↦ Φ α hα n`, and `Φ_α` itself is not formed.
* **Condition (1a).** "`Φ_α` is a nonempty subset of `Ψ_α`": the subset part is typing, and
  nonemptiness of the union over `n` is stated faithfully as `∃ n, (Φ α hα n).Nonempty`.  The
  stronger `(Φ α hα 0).Nonempty` is then derived (Proposition 3.5), by condition (1e).
* **The inclusions `i_{m,n}`.** Larson's `i_m`, the identity on `X_m` viewed in `I_{m,n}`, is
  `Fin.castLEEmb h : Fin m ↪ Fin n` (`h : m ≤ n`); `i_n ∈ I_{n,n+1}` is
  `Fin.castLEEmb (Nat.le_succ n)`, and `i_n ∈ I_{n,n+m}` is `Fin.castLEEmb (Nat.le_add_right n m)`.
* **Ordinal side conditions.** A level is indexed by `α` together with a proof `hα : α < δ`.
  Conditions quantified over "`α + 1 < δ`" take `hα : α + 1 < δ` and use `α < δ` derived from
  it; conditions over "`α < β < δ`" take `hαβ : α < β` and `hβ : β < δ`.  Vertical projections
  take the proof of `≤` as their argument: in (2b) the left projection is `V_{α+1,β}` (by
  `Order.add_one_le_of_lt hαβ`) and the right one is `V_{α,β}` (by `hαβ.le`).
* **Nonzero length.** Larson requires `δ ≠ 0`; this is the field `pos : 0 < δ`.
* **Proposition 4.1** omits the hypothesis `m ≤ n` (implied by the existence of an injection
  `Fin m ↪ Fin n`) and holds with no hypothesis on `φ`; the stated version keeps `φ ∈ Φ^m_β`
  out of the signature, so it is (formally) stronger than Larson's.
* **Proposition 4.2.** Larson's union over `ψ ∈ V_{α,α+1}^{-1}[{φ}]` ranges over `ψ ∈ Φ^n_{α+1}`
  (for `ψ` outside the process `E(ψ)` is unconstrained and the inclusion from left to right
  fails); the hypothesis `φ ∈ Φ^n_α` is not needed and is omitted.
-/

open Order InfinitaryLogic.ScottProcess.FreeArray

universe w

noncomputable section

namespace InfinitaryLogic

/-- A **Scott process** of length `δ` over the level-`0` data `A` (Larson, Scott processes,
Definition 3.1): a level `Φ α hα n ⊆ Ψ^n_α` for every `α < δ` and every column `n`, satisfying
the formula conditions (1a)–(1e) and the coherence conditions (2a)–(2c). -/
structure ScottProcess (A : AtomicData.{w}) (δ : Ordinal.{0}) where
  /-- The levels: `Φ α hα n` is Larson's `Φ^n_α = Φ_α ∩ Ψ^n_α`. -/
  Φ : ∀ α < δ, ∀ n, Set (Ψ A α n)
  /-- The length is nonzero. -/
  pos : 0 < δ
  /-- Condition (1a): each level is nonempty (in some column). -/
  nonempty : ∀ α (hα : α < δ), ∃ n, (Φ α hα n).Nonempty
  /-- Condition (1b): extension sets of members of `Φ_{α+1}` lie in `Φ_α`. -/
  E_subset : ∀ α (hα : α + 1 < δ) n, ∀ φ ∈ Φ (α + 1) hα n,
    E φ ⊆ Φ α ((lt_add_one α).trans hα) (n + 1)
  /-- Condition (1c): `Φ_α = V_{α,β}[Φ_β]` for `α < β < δ`. -/
  eq_image_V : ∀ α β (hαβ : α < β) (hβ : β < δ) n,
    Φ α (hαβ.trans hβ) n = V hαβ.le '' Φ β hβ n
  /-- Condition (1d): closure under `H^n_α(·, j)` for `j ∈ I_{n,n}`. -/
  H_mem : ∀ α (hα : α < δ) n (j : Fin n ↪ Fin n), ∀ φ ∈ Φ α hα n, H j φ ∈ Φ α hα n
  /-- Condition (1e): `Φ^m_α = H^n_α[Φ^n_α × {i_m}]` for `m < n`. -/
  eq_image_H : ∀ α (hα : α < δ) m n (hmn : m < n),
    Φ α hα m = H (Fin.castLEEmb hmn.le) '' Φ α hα n
  /-- Condition (2a): `E(φ) = V_{α,α+1}[{ψ ∈ Φ^{n+1}_{α+1} | H^{n+1}_{α+1}(ψ, i_n) = φ}]`. -/
  E_eq : ∀ α (hα : α + 1 < δ) n, ∀ φ ∈ Φ (α + 1) hα n,
    E φ = V (lt_add_one α).le ''
      {ψ ∈ Φ (α + 1) hα (n + 1) | H (Fin.castLEEmb (Nat.le_succ n)) ψ = φ}
  /-- Condition (2b): `E(V_{α+1,β}(φ)) ⊆ V_{α,β}[{ψ ∈ Φ^{n+1}_β | H^{n+1}_β(ψ, i_n) = φ}]`
  for `α < β < δ`. -/
  E_V_subset : ∀ α β (hαβ : α < β) (hβ : β < δ) n, ∀ φ ∈ Φ β hβ n,
    E (V (add_one_le_of_lt hαβ) φ) ⊆
      V hαβ.le '' {ψ ∈ Φ β hβ (n + 1) | H (Fin.castLEEmb (Nat.le_succ n)) ψ = φ}
  /-- Condition (2c), amalgamation: any `φ ∈ Φ^n_α` and `ψ ∈ Φ^m_α` are restrictions of one
  `θ ∈ Φ^{n+m}_α`, along `i_n` and along some `j ∈ I_{m,n+m}` respectively. -/
  amalgamate : ∀ α (hα : α < δ) n m, ∀ φ ∈ Φ α hα n, ∀ ψ ∈ Φ α hα m,
    ∃ θ ∈ Φ α hα (n + m), ∃ j : Fin m ↪ Fin (n + m),
      φ = H (Fin.castLEEmb (Nat.le_add_right n m)) θ ∧ ψ = H j θ

namespace ScottProcess

variable {A : AtomicData.{w}} {δ : Ordinal.{0}} (P : ScottProcess A δ)

/-! ### Projections within a process -/

/-- Every injection `Fin m ↪ Fin n` is the inclusion `i_{m,n}` followed by a permutation. -/
theorem exists_equiv_castLE_eq {m n : ℕ} (hmn : m ≤ n) (j : Fin m ↪ Fin n) :
    ∃ e : Fin n ≃ Fin n, ∀ i : Fin m, e (Fin.castLE hmn i) = j i := by
  classical
  let f : Fin n → Fin n := fun i ↦ if h : (i : ℕ) < m then j ⟨i, h⟩ else i
  have hf : ∀ i : Fin m, f (Fin.castLE hmn i) = j i := fun i ↦ by
    simp only [f, Fin.val_castLE, i.2, ↓reduceDIte]
  obtain ⟨g, hg⟩ := Set.MapsTo.exists_equiv_extend_of_card_eq
    (t := (Finset.univ : Finset (Fin n))) (s := Set.range (Fin.castLE hmn)) (f := f)
    Finset.card_univ.symm (fun _ _ ↦ Finset.mem_coe.2 (Finset.mem_univ _))
    (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
      rw [hf, hf] at hab
      rw [j.injective hab])
  refine ⟨g.trans (Equiv.subtypeUnivEquiv Finset.mem_univ), fun i ↦ ?_⟩
  rw [Equiv.trans_apply, Equiv.subtypeUnivEquiv_apply, hg _ ⟨i, rfl⟩, hf]

/-- Vertical projections of members of the process are members (condition (1c), including the
trivial case `α = β`). -/
theorem V_mem {α β : Ordinal.{0}} (hαβ : α ≤ β) (hβ : β < δ) {n : ℕ} {φ : Ψ A β n}
    (hφ : φ ∈ P.Φ β hβ n) : V hαβ φ ∈ P.Φ α (hαβ.trans_lt hβ) n := by
  rcases hαβ.eq_or_lt with rfl | hlt
  · rwa [V_self]
  · rw [P.eq_image_V α β hlt hβ n]
    exact ⟨φ, hφ, rfl⟩

/-- **Remark 3.4** (Larson, Scott processes): conditions (1d) and (1e) give
`Φ^m_α = H^n_α[Φ^n_α × {j}]` for every `j ∈ I_{m,n}`. -/
theorem image_H_eq (α : Ordinal.{0}) (hα : α < δ) {m n : ℕ} (j : Fin m ↪ Fin n) :
    P.Φ α hα m = H j '' P.Φ α hα n := by
  have hmn : m ≤ n := Fin.nonempty_embedding_iff.1 ⟨j⟩
  obtain ⟨e, he⟩ := exists_equiv_castLE_eq hmn j
  have hj : j = (Fin.castLEEmb hmn).trans e.toEmbedding :=
    Function.Embedding.ext fun i ↦ (he i).symm
  have base : P.Φ α hα m = H (Fin.castLEEmb hmn) '' P.Φ α hα n := by
    rcases hmn.eq_or_lt with rfl | hlt
    · have : Fin.castLEEmb hmn = Function.Embedding.refl (Fin m) :=
        Function.Embedding.ext fun i ↦ Fin.ext rfl
      rw [this]
      simp only [H_id, Set.image_id']
    · exact P.eq_image_H α hα m n hlt
  have perm : H e.toEmbedding '' P.Φ α hα n = P.Φ α hα n := by
    refine Set.Subset.antisymm ?_ fun φ hφ ↦ ?_
    · rintro _ ⟨φ, hφ, rfl⟩
      exact P.H_mem α hα n _ φ hφ
    · refine ⟨H e.symm.toEmbedding φ, P.H_mem α hα n _ φ hφ, ?_⟩
      rw [H_comp]
      have : e.toEmbedding.trans e.symm.toEmbedding = Function.Embedding.refl (Fin n) :=
        Function.Embedding.ext fun i ↦ e.symm_apply_apply i
      rw [this, H_id]
  rw [hj, base]
  conv_lhs => rw [← perm]
  rw [Set.image_image]
  exact Set.image_congr fun φ _ ↦ H_comp _ _ φ

/-! ### Proposition 3.5 -/

/-- Proposition 3.5, existence: each `Φ^0_α` is nonempty (by conditions (1a) and (1e)). -/
theorem nonempty_zero (α : Ordinal.{0}) (hα : α < δ) : (P.Φ α hα 0).Nonempty := by
  obtain ⟨n, φ, hφ⟩ := P.nonempty α hα
  rw [P.image_H_eq α hα (Fin.castLEEmb (Nat.zero_le n))]
  exact ⟨_, φ, hφ, rfl⟩

/-- Proposition 3.5, uniqueness: each `Φ^0_α` has at most one element (by condition (2c)). -/
theorem subsingleton_zero (α : Ordinal.{0}) (hα : α < δ) : (P.Φ α hα 0).Subsingleton := by
  intro φ hφ ψ hψ
  obtain ⟨θ, -, j, rfl, rfl⟩ := P.amalgamate α hα 0 0 φ hφ ψ hψ
  rw [Subsingleton.elim j (Fin.castLEEmb (Nat.le_add_right 0 0))]

/-- **Proposition 3.5** (Larson, Scott processes): for each `α < δ`, `Φ^0_α` has a unique
element. -/
theorem existsUnique_mem_zero (α : Ordinal.{0}) (hα : α < δ) : ∃! φ, φ ∈ P.Φ α hα 0 := by
  obtain ⟨φ, hφ⟩ := P.nonempty_zero α hα
  exact ⟨φ, hφ, fun ψ hψ ↦ P.subsingleton_zero α hα hψ hφ⟩

/-- The remark after Proposition 3.5 (Larson, Scott processes): if `α + 1 < δ` and `φ` is the
unique element of `Φ^0_{α+1}`, then `E(φ) = Φ^1_α`. -/
theorem E_eq_of_mem_zero (α : Ordinal.{0}) (hα : α + 1 < δ) {φ : Ψ A (α + 1) 0}
    (hφ : φ ∈ P.Φ (α + 1) hα 0) : E φ = P.Φ α ((lt_add_one α).trans hα) 1 := by
  rw [P.E_eq α hα 0 φ hφ, P.eq_image_V α (α + 1) (lt_add_one α) hα 1]
  congr 1
  refine Set.sep_eq_self_iff_mem_true.2 fun ψ hψ ↦ P.subsingleton_zero (α + 1) hα ?_ hφ
  rw [P.image_H_eq (α + 1) hα (Fin.castLEEmb (Nat.le_succ 0))]
  exact ⟨ψ, hψ, rfl⟩

/-! ### Section 4: consequences of coherence -/

/-- **Proposition 4.1** (Larson, Scott processes): for `α ≤ β < δ` and `j ∈ I_{m,n}`,
`V_{α,β}[{ψ ∈ Φ^n_β | H^n_β(ψ, j) = φ}] ⊆ {θ ∈ Φ^n_α | H^n_α(θ, j) = V_{α,β}(φ)}`.
(Larson assumes `φ ∈ Φ^m_β`; the inclusion holds for every `φ ∈ Ψ^m_β`.) -/
theorem image_V_fiber_subset {α β : Ordinal.{0}} (hαβ : α ≤ β) (hβ : β < δ) {m n : ℕ}
    (j : Fin m ↪ Fin n) (φ : Ψ A β m) :
    V hαβ '' {ψ ∈ P.Φ β hβ n | H j ψ = φ} ⊆
      {θ ∈ P.Φ α (hαβ.trans_lt hβ) n | H j θ = V hαβ φ} := by
  rintro _ ⟨ψ, ⟨hψ, rfl⟩, rfl⟩
  exact ⟨P.V_mem hαβ hβ hψ, (V_H_comm hαβ j ψ).symm⟩

/-- **Proposition 4.2** (Larson, Scott processes): for `α + 1 < δ` and `φ ∈ Ψ^n_α`,
`⋃ {E(ψ) | ψ ∈ Φ^n_{α+1}, V_{α,α+1}(ψ) = φ} = {θ ∈ Φ^{n+1}_α | H^{n+1}_α(θ, i_n) = φ}`. -/
theorem biUnion_E_eq (α : Ordinal.{0}) (hα : α + 1 < δ) {n : ℕ} (φ : Ψ A α n) :
    ⋃ ψ ∈ {ψ ∈ P.Φ (α + 1) hα n | V (lt_add_one α).le ψ = φ}, E ψ =
      {θ ∈ P.Φ α ((lt_add_one α).trans hα) (n + 1) |
        H (Fin.castLEEmb (Nat.le_succ n)) θ = φ} := by
  refine Set.Subset.antisymm ?_ fun θ ⟨hθ, hHθ⟩ ↦ ?_
  · refine Set.iUnion₂_subset fun ψ ⟨hψ, hVψ⟩ ↦ ?_
    rw [P.E_eq α hα n ψ hψ, ← hVψ]
    exact P.image_V_fiber_subset (lt_add_one α).le hα _ ψ
  · rw [P.eq_image_V α (α + 1) (lt_add_one α) hα (n + 1)] at hθ
    obtain ⟨ψ', hψ', rfl⟩ := hθ
    have hψ : H (Fin.castLEEmb (Nat.le_succ n)) ψ' ∈ P.Φ (α + 1) hα n := by
      rw [P.eq_image_H (α + 1) hα n (n + 1) (Nat.lt_succ_self n)]
      exact ⟨ψ', hψ', rfl⟩
    refine Set.mem_biUnion (x := H (Fin.castLEEmb (Nat.le_succ n)) ψ')
      ⟨hψ, by rw [V_H_comm, hHθ]⟩ ?_
    rw [P.E_eq α hα n _ hψ]
    exact ⟨ψ', ⟨hψ', rfl⟩, rfl⟩

/-- The reverse inclusion of condition (2b), the common core of Propositions 4.3 and 4.4:
`V_{α,β}[{ψ ∈ Φ^{n+1}_β | H^{n+1}_β(ψ, i_n) = φ}] ⊆ E(V_{α+1,β}(φ))`. -/
theorem image_V_fiber_subset_E {α β : Ordinal.{0}} (hαβ : α < β) (hβ : β < δ) {n : ℕ}
    {φ : Ψ A β n} (hφ : φ ∈ P.Φ β hβ n) :
    V hαβ.le '' {ψ ∈ P.Φ β hβ (n + 1) | H (Fin.castLEEmb (Nat.le_succ n)) ψ = φ} ⊆
      E (V (add_one_le_of_lt hαβ) φ) := by
  have h1 : α + 1 ≤ β := add_one_le_of_lt hαβ
  rintro _ ⟨ψ, ⟨hψ, hHψ⟩, rfl⟩
  rw [P.E_eq α (h1.trans_lt hβ) n _ (P.V_mem h1 hβ hφ)]
  refine ⟨V h1 ψ, ⟨P.V_mem h1 hβ hψ, by rw [← V_H_comm, hHψ]⟩, ?_⟩
  exact V_comp _ h1 ψ

/-- **Proposition 4.4** (Larson, Scott processes): equality holds in condition (2b): for
`α < β < δ` and `φ ∈ Φ^n_β`,
`E(V_{α+1,β}(φ)) = V_{α,β}[{ψ ∈ Φ^{n+1}_β | H^{n+1}_β(ψ, i_n) = φ}]`. -/
theorem E_V_eq {α β : Ordinal.{0}} (hαβ : α < β) (hβ : β < δ) {n : ℕ} {φ : Ψ A β n}
    (hφ : φ ∈ P.Φ β hβ n) :
    E (V (add_one_le_of_lt hαβ) φ) =
      V hαβ.le '' {ψ ∈ P.Φ β hβ (n + 1) | H (Fin.castLEEmb (Nat.le_succ n)) ψ = φ} :=
  (P.E_V_subset α β hαβ hβ n φ hφ).antisymm (P.image_V_fiber_subset_E hαβ hβ hφ)

/-- **Proposition 4.3** (Larson, Scott processes): for `α ≤ β` with `β + 1 < δ` and
`φ ∈ Φ_{β+1}`, `E(V_{α+1,β+1}(φ)) = V_{α,β}[E(φ)]`. -/
theorem E_V_add_one_eq {α β : Ordinal.{0}} (hαβ : α ≤ β) (hβ : β + 1 < δ) {n : ℕ}
    {φ : Ψ A (β + 1) n} (hφ : φ ∈ P.Φ (β + 1) hβ n) :
    E (V (add_one_le_of_lt (lt_add_one_iff.2 hαβ)) φ) = V hαβ '' E φ := by
  rw [P.E_eq β hβ n φ hφ, Set.image_image]
  have := P.E_V_eq (lt_add_one_iff.2 hαβ) hβ hφ
  convert this using 1
  exact Set.image_congr fun ψ _ ↦ V_comp _ _ ψ

end ScottProcess

/-! ### Trivial and toy instances -/

namespace ScottProcess

/-- The one-point level-`0` data: a single atomic type in every column. -/
def unitData : AtomicData.{w} where
  Ψ0 _ := PUnit
  H0 _ _ _ _ := PUnit.unit
  H0_id _ _ := rfl
  H0_comp _ _ _ _ _ _ := rfl

/-- Over the one-point data every column of every row is a singleton. -/
theorem unitData_subsingleton_nonempty (α : Ordinal.{0}) (n : ℕ) :
    Subsingleton (Ψ unitData.{w} α n) ∧ Nonempty (Ψ unitData.{w} α n) := by
  induction α using Ordinal.limitRecOn generalizing n with
  | zero =>
    exact ⟨@Equiv.subsingleton _ _ (zeroEquiv unitData n) (inferInstanceAs (Subsingleton PUnit)),
      ⟨(zeroEquiv unitData n).symm PUnit.unit⟩⟩
  | add_one α ih =>
    obtain ⟨h1, ⟨x⟩⟩ := ih n
    obtain ⟨h2, ⟨y⟩⟩ := ih (n + 1)
    refine ⟨?_, ⟨(succEquiv unitData α n).symm (x, ⟨Set.univ, ⟨y, trivial⟩⟩)⟩⟩
    have : Subsingleton (succΨ (level unitData.{w} α) n) :=
      ⟨fun a b ↦ Prod.ext (Subsingleton.elim _ _)
        (Subtype.ext (a.2.2.eq_univ.trans b.2.2.eq_univ.symm))⟩
    exact (succEquiv unitData α n).subsingleton
  | limit lam hlam ih =>
    refine ⟨?_, ?_⟩
    · have : Subsingleton (Thread lam (fun β _ ↦ level unitData.{w} β) n) :=
        ⟨fun a b ↦ Subtype.ext (funext fun β ↦ funext fun h ↦ (ih β h n).1.elim _ _)⟩
      exact (limEquiv unitData hlam n).subsingleton
    · obtain ⟨φ, -⟩ := exists_limit_of_thread (A := unitData) hlam
        (fun β h ↦ Classical.choice (ih β h n).2)
        (fun β h ↦ (ih β ((lt_add_one β).trans h) n).1.elim _ _)
        (fun β h _ δ hδ ↦ (ih δ (hδ.trans h) n).1.elim _ _)
      exact ⟨φ⟩

/-- Over the one-point data every column is a subsingleton. -/
instance (α : Ordinal.{0}) (n : ℕ) : Subsingleton (Ψ unitData.{w} α n) :=
  (unitData_subsingleton_nonempty α n).1

/-- Over the one-point data every column is nonempty. -/
instance (α : Ordinal.{0}) (n : ℕ) : Nonempty (Ψ unitData.{w} α n) :=
  (unitData_subsingleton_nonempty α n).2

/-- Over the one-point data, every set of the shape on the right of conditions (2a) and (2b)
is the full column. -/
theorem unitData_image_V_fiber {α β : Ordinal.{0}} (h : β ≤ α) {n m : ℕ} (j : Fin m ↪ Fin n)
    (φ : Ψ unitData.{w} α m) :
    V h '' {ψ ∈ (Set.univ : Set (Ψ unitData.{w} α n)) | H j ψ = φ} = Set.univ :=
  Set.Nonempty.eq_univ
    ⟨_, Classical.arbitrary _, ⟨Set.mem_univ _, Subsingleton.elim _ _⟩, rfl⟩

/-- The trivial Scott process of length `δ > 0` over the one-point data: every level is the full
column.  All conditions of Definition 3.1 hold because every column is a singleton. -/
def unitProcess (δ : Ordinal.{0}) (hδ : 0 < δ) : ScottProcess unitData.{w} δ where
  Φ _ _ _ := Set.univ
  pos := hδ
  nonempty _ _ := ⟨0, Set.univ_nonempty⟩
  E_subset _ _ _ _ _ := Set.subset_univ _
  eq_image_V _ _ _ _ _ := (Set.univ_nonempty.image _).eq_univ.symm
  H_mem _ _ _ _ _ _ := Set.mem_univ _
  eq_image_H _ _ _ _ _ := (Set.univ_nonempty.image _).eq_univ.symm
  E_eq _ _ _ φ _ := (E_nonempty φ).eq_univ.trans (unitData_image_V_fiber _ _ _).symm
  E_V_subset _ _ _ _ _ _ _ := by
    rw [unitData_image_V_fiber]
    exact Set.subset_univ _
  amalgamate _ _ n _ _ _ _ _ := ⟨Classical.arbitrary _, Set.mem_univ _, Fin.natAddEmb n,
    Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- Every level of `unitProcess` is the full column. -/
@[simp] theorem unitProcess_Φ (δ : Ordinal.{0}) (hδ : 0 < δ) (α : Ordinal.{0}) (hα : α < δ)
    (n : ℕ) : (unitProcess.{w} δ hδ).Φ α hα n = Set.univ :=
  rfl

end ScottProcess

end InfinitaryLogic

end
