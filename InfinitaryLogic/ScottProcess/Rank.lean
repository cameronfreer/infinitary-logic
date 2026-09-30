/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ScottProcess.Basic

/-!
# Stabilization and rank of a Scott process

The rank of a Scott process (Larson, *Scott processes*, Definition 5.6): the least level `β`
at which the vertical projection `V_{β,β+1}` is injective on `Φ_{β+1}`.  Stabilization
propagates upward (Proposition 5.5), and it is forced `n` levels above a level `β` either by
injectivity at `β` on the columns above `n` (Remark 5.7) or by injectivity beyond a single
member of `Φ^n_β` (Definition 5.8, Proposition 5.13).

## Main declarations

* `ScottProcess.StabilizesAt β`: `β + 1 < δ` and `V_{β,β+1}` is injective on every column of
  `Φ_{β+1}`; `ScottProcess.stabilizesAt_iff_bijOn` restates it as a bijection
  `Φ^n_{β+1} → Φ^n_β` on every column.
* `ScottProcess.Terminating`, `ScottProcess.IsRank`, `ScottProcess.rank` (Definition 5.6),
  with `ScottProcess.isRank_rank`, `ScottProcess.IsRank.unique`, `ScottProcess.isRank_iff`.
* `ScottProcess.stabilizesAt_of_le`: Proposition 5.5, stabilization propagates upward.
* `ScottProcess.stabilizesAt_add_nat`: Remark 5.7.
* `ScottProcess.InjectiveBeyond` (Definition 5.8) and
  `ScottProcess.stabilizesAt_of_injectiveBeyond` (Proposition 5.13).
* `ScottProcess.unitProcess_terminating_iff`, `ScottProcess.unitProcess_rank`: the toy process
  has rank `0` when `1 < δ`, and does not terminate at length `1`.

Proposition 5.1(1), Corollaries 5.2 and 5.3 and the induction of Remark 5.9 are proved as
private steps of the proofs above.

## Interpretation choices

* **Column-wise stabilization.** Since `V` preserves columns, injectivity of `V_{β,β+1}` on
  Larson's `Φ_{β+1} = ⋃ n, Φ^n_{β+1}` is injectivity on every column `Φ^n_{β+1}`.
* **The length condition is part of stabilization.** `StabilizesAt β` asserts `β + 1 < δ`
  (as `∃ h : β + 1 < δ, …`), so no level at or past the end of the process is a stabilization
  level; a formulation `∀ h : β + 1 < δ, …` would hold vacuously there and make every process
  terminate.
* **Partial rank.** Larson's rank is undefined for a nonterminating process.  `rank` takes a
  proof of `Terminating` and is the `sInf` of the (nonempty) set of stabilization levels; there
  is no default value.  `IsRank β` is the proof-free predicate (`β` is the least stabilization
  level).
* **No `+ 1`.** The rank is the least stabilization level itself, as in Definition 5.6, so the
  process of the infinite pure set has rank `0`.  This differs by one from conventions that
  count the level at which stabilization is witnessed.
* **`Ordinal.{0}`.** Ranks live in `Ordinal.{0}`, the index type of the rows of the free array.
* **Levels instead of lengths.** Larson states Remark 5.7 and Proposition 5.13 for processes
  of lengths `γ > β + n + 1` and `β + n + 2`; here they are stated for a process of any length
  `δ` with `β + n + 1 < δ`.  Stabilization at `β + n` only involves the levels `β + n` and
  `β + n + 1`, so the two forms agree.
* **Definition 5.8.** "`V_{β,β+1}^{-1}[{ψ}] ∩ Φ_{β+1}` is a singleton" is `∃!`; Larson's
  standing hypothesis `φ ∈ Φ^n_β` is kept out of the definition and assumed where it is used,
  and his `m ∈ ω \ n` is implied by the existence of `j : Fin n ↪ Fin m`.

## References

* Paul B. Larson, *Scott processes*, in *Beyond First Order Model Theory*, vol. I
  (J. Iovino, ed.), CRC Press, 2017, ch. 2, §5.  Numbering follows the book; §5 is numbered
  identically in the 2016 preprint.
-/

open Order InfinitaryLogic.ScottProcess.FreeArray

universe w

noncomputable section

namespace InfinitaryLogic

namespace ScottProcess

variable {A : AtomicData.{w}} {δ : Ordinal.{0}} (P : ScottProcess A δ)

/-! ### Stabilization -/

/-- The process **stabilizes at `β`**: `β + 1 < δ`, and `V_{β,β+1}` is injective on every
column `Φ^n_{β+1}` (the condition of Larson, Definition 5.6). -/
def StabilizesAt (β : Ordinal.{0}) : Prop :=
  ∃ h : β + 1 < δ, ∀ n, Set.InjOn (V (A := A) (n := n) (lt_add_one β).le) (P.Φ (β + 1) h n)

/-- Stabilization as a bijection of levels: the process stabilizes at `β` iff `β + 1 < δ` and
`V_{β,β+1}` maps every column `Φ^n_{β+1}` bijectively onto `Φ^n_β` (surjectivity is condition
(1c)). -/
theorem stabilizesAt_iff_bijOn (β : Ordinal.{0}) :
    P.StabilizesAt β ↔ ∃ h : β + 1 < δ, ∀ n,
      Set.BijOn (V (lt_add_one β).le) (P.Φ (β + 1) h n) (P.Φ β ((lt_add_one β).trans h) n) := by
  refine ⟨fun ⟨h, hn⟩ ↦ ⟨h, fun n ↦ ⟨fun x hx ↦ P.V_mem _ h hx, hn n, ?_⟩⟩,
    fun ⟨h, hn⟩ ↦ ⟨h, fun n ↦ (hn n).injOn⟩⟩
  rw [P.eq_image_V β (β + 1) (lt_add_one β) h n]
  exact Set.surjOn_image _ _

/-! ### Fibers of the vertical projections -/

/-- The fiber `V_{α,β}^{-1}[{φ}] ∩ Φ^n_β` of `φ ∈ Ψ^n_α` in level `β` of the process. -/
private def fiber {α β : Ordinal.{0}} (hαβ : α ≤ β) (hβ : β < δ) {n : ℕ} (φ : Ψ A α n) :
    Set (Ψ A β n) :=
  {ψ ∈ P.Φ β hβ n | V hαβ ψ = φ}

/-- Fibers over members of the process are nonempty (condition (1c)). -/
private theorem fiber_nonempty {α β : Ordinal.{0}} (hαβ : α ≤ β) (hβ : β < δ) {n : ℕ}
    {φ : Ψ A α n} (hφ : φ ∈ P.Φ α (hαβ.trans_lt hβ) n) : (P.fiber hαβ hβ φ).Nonempty := by
  rcases hαβ.eq_or_lt with rfl | hlt
  · exact ⟨φ, hφ, V_self _ _⟩
  · rw [P.eq_image_V α β hlt hβ n] at hφ
    obtain ⟨ψ, hψ, rfl⟩ := hφ
    exact ⟨ψ, hψ, rfl⟩

/-- Fibers over the diagonal are subsingletons. -/
private theorem fiber_self_subsingleton {α : Ordinal.{0}} (h : α ≤ α) (hα : α < δ) {n : ℕ}
    (φ : Ψ A α n) : (P.fiber h hα φ).Subsingleton := by
  rintro x ⟨-, hx⟩ y ⟨-, hy⟩
  rw [V_self] at hx hy
  rw [hx, hy]

/-- Injectivity of `V_{α,β}` on a column of `Φ_β` is subsingletonness of the fibers over that
column of `Φ_α`. -/
private theorem injOn_iff_fiber_subsingleton {α β : Ordinal.{0}} (hαβ : α ≤ β) (hβ : β < δ)
    (n : ℕ) :
    Set.InjOn (V hαβ) (P.Φ β hβ n) ↔
      ∀ φ ∈ P.Φ α (hαβ.trans_lt hβ) n, (P.fiber hαβ hβ φ).Subsingleton :=
  ⟨fun h _ _ _ ⟨hx, hxφ⟩ _ ⟨hy, hyφ⟩ ↦ h hx hy (hxφ.trans hyφ.symm),
    fun h _ hx _ hy hxy ↦ h _ (P.V_mem hαβ hβ hx) ⟨hx, rfl⟩ ⟨hy, hxy.symm⟩⟩

/-- Equal projections to a row stay equal under further projection. -/
private theorem V_eq_V_of_le {α β γ : Ordinal.{0}} (hβ : β ≤ α) (hγ : γ ≤ β) {n : ℕ}
    {x y : Ψ A α n} (h : V hβ x = V hβ y) : V (hγ.trans hβ) x = V (hγ.trans hβ) y := by
  rw [← V_comp hγ hβ, ← V_comp hγ hβ, h]

/-! ### Proposition 5.1(1) and Corollaries 5.2, 5.3 -/

/-- Proposition 5.1(1), subsingleton form: if `V_{β,β+1}^{-1}[{ψ}] ∩ Φ_{β+1}` is a
subsingleton for each `ψ ∈ E(φ)`, then so is `V_{β+1,β+2}^{-1}[{φ}] ∩ Φ_{β+2}`. -/
private theorem fiber_subsingleton_of_forall_E {β : Ordinal.{0}} (hβ : β + 1 + 1 < δ) {n : ℕ}
    {φ : Ψ A (β + 1) n}
    (h : ∀ ψ ∈ E φ, (P.fiber (lt_add_one β).le ((lt_add_one _).trans hβ) ψ).Subsingleton) :
    (P.fiber (lt_add_one (β + 1)).le hβ φ).Subsingleton := by
  -- `E(φ_i) ⊆ Φ_{β+1}` and `V_{β,β+1}[E(φ_i)] = E(φ)` (Proposition 4.3).
  have key : ∀ φ₁ ∈ P.fiber (lt_add_one (β + 1)).le hβ φ,
      ∀ φ₂ ∈ P.fiber (lt_add_one (β + 1)).le hβ φ, E φ₁ ⊆ E φ₂ := by
    rintro φ₁ ⟨h₁, rfl⟩ φ₂ ⟨h₂, he⟩ θ hθ
    have e₁ := P.E_V_add_one_eq (lt_add_one β).le hβ h₁
    have e₂ := P.E_V_add_one_eq (lt_add_one β).le hβ h₂
    obtain ⟨θ', hθ'E, hθθ'⟩ : V (lt_add_one β).le θ ∈ V (lt_add_one β).le '' E φ₂ := by
      rw [← e₂, he, e₁]
      exact ⟨θ, hθ, rfl⟩
    have hmem : V (lt_add_one β).le θ ∈ E (V (lt_add_one (β + 1)).le φ₁) := by
      rw [e₁]
      exact ⟨θ, hθ, rfl⟩
    rw [h _ hmem ⟨P.E_subset (β + 1) hβ n φ₁ h₁ hθ, rfl⟩
      ⟨P.E_subset (β + 1) hβ n φ₂ h₂ hθ'E, hθθ'⟩]
    exact hθ'E
  intro φ₁ h₁ φ₂ h₂
  exact Ψ.ext_succ (h₁.2.trans h₂.2.symm) ((key φ₁ h₁ φ₂ h₂).antisymm (key φ₂ h₂ φ₁ h₁))

/-- Corollary 5.2: if `V_{β,β+1}` is injective on `Φ^{n+1}_{β+1}`, then `V_{β+1,β+2}` is
injective on `Φ^n_{β+2}`. -/
private theorem injOn_succ_of_injOn {β : Ordinal.{0}} (hβ : β + 1 + 1 < δ) {n : ℕ}
    (h : Set.InjOn (V (A := A) (n := n + 1) (lt_add_one β).le)
      (P.Φ (β + 1) ((lt_add_one _).trans hβ) (n + 1))) :
    Set.InjOn (V (A := A) (n := n) (lt_add_one (β + 1)).le) (P.Φ (β + 1 + 1) hβ n) := by
  rw [P.injOn_iff_fiber_subsingleton] at h ⊢
  exact fun φ hφ ↦ P.fiber_subsingleton_of_forall_E hβ fun ψ hψ ↦
    h ψ (P.E_subset β ((lt_add_one _).trans hβ) n φ hφ hψ)

/-- The subsingleton core of Corollary 5.3: for `β + 1 ≤ η < δ`, `φ ∈ Ψ^n_{β+1}` and
`ψ ∈ E(φ)`, if `V_{β,η}^{-1}[{ψ}] ∩ Φ_η` is a subsingleton then so is
`V_{β+1,η}^{-1}[{φ}] ∩ Φ_η`. -/
private theorem fiber_subsingleton_of_mem_E {β η : Ordinal.{0}} (hβη : β + 1 ≤ η) (hη : η < δ)
    {n : ℕ} {φ : Ψ A (β + 1) n} {ψ : Ψ A β (n + 1)} (hψ : ψ ∈ E φ)
    (h : (P.fiber ((lt_add_one β).le.trans hβη) hη ψ).Subsingleton) :
    (P.fiber hβη hη φ).Subsingleton := by
  have hlt : β < η := (lt_add_one β).trans_le hβη
  suffices key : ∀ φ' ∈ P.fiber hβη hη φ,
      ∃ ρ ∈ P.fiber hlt.le hη ψ, φ' = H (Fin.castLEEmb (Nat.le_succ n)) ρ by
    intro a ha b hb
    obtain ⟨ρa, hρa, rfl⟩ := key a ha
    obtain ⟨ρb, hρb, rfl⟩ := key b hb
    rw [h hρa hρb]
  rintro φ' ⟨h', rfl⟩
  obtain ⟨ρ, ⟨hρ, hHρ⟩, rfl⟩ : ψ ∈ V hlt.le ''
      {ρ ∈ P.Φ η hη (n + 1) | H (Fin.castLEEmb (Nat.le_succ n)) ρ = φ'} := by
    rw [← P.E_V_eq hlt hη h']
    exact hψ
  exact ⟨ρ, ⟨hρ, rfl⟩, hHρ.symm⟩

/-! ### Proposition 5.5 -/

/-- If the process stabilizes at every level in `[β, γ)`, then `V_{β,γ}` is injective on
`Φ_γ`. -/
private theorem injOn_V_of_forall_stabilizesAt {β γ : Ordinal.{0}} (hβγ : β ≤ γ) (hγ : γ < δ)
    (h : ∀ η, β ≤ η → η < γ → P.StabilizesAt η) (n : ℕ) :
    Set.InjOn (V (A := A) (n := n) hβγ) (P.Φ γ hγ n) := by
  rcases hβγ.eq_or_lt with rfl | hlt
  · intro x _ y _ hxy
    rwa [V_self, V_self] at hxy
  induction γ using Ordinal.limitRecOn with
  | zero => exact absurd hlt (not_lt.2 zero_le)
  | add_one γ ih =>
    have hβγ' : β ≤ γ := lt_add_one_iff.1 hlt
    intro x hx y hy hxy
    rw [← V_comp hβγ' (lt_add_one γ).le, ← V_comp hβγ' (lt_add_one γ).le] at hxy
    obtain ⟨_, hinj⟩ := h γ hβγ' (lt_add_one γ)
    refine hinj n hx hy ?_
    rcases hβγ'.eq_or_lt with rfl | hlt'
    · rwa [V_self, V_self] at hxy
    exact ih hβγ' ((lt_add_one γ).trans hγ) (fun η h1 h2 ↦ h η h1 (h2.trans (lt_add_one γ)))
      hlt' (P.V_mem _ hγ hx) (P.V_mem _ hγ hy) hxy
  | limit γ hγl ih =>
    intro x hx y hy hxy
    refine Ψ.ext_limit hγl fun η hη ↦ ?_
    rcases lt_or_ge β η with hβη | hηβ
    · refine ih η hη hβη.le (hη.trans hγ) (fun ζ h1 h2 ↦ h ζ h1 (h2.trans hη)) hβη
        (P.V_mem _ hγ hx) (P.V_mem _ hγ hy) ?_
      rw [V_comp, V_comp]
      exact hxy
    · exact V_eq_V_of_le hβγ hηβ hxy

/-- The inductive step of Proposition 5.5: if `β < γ`, `γ + 1 < δ` and `V_{β,γ}` is injective
on `Φ_γ`, then the process stabilizes at `γ`. -/
private theorem stabilizesAt_of_injOn_V {β γ : Ordinal.{0}} (hβγ : β < γ) (hγ : γ + 1 < δ)
    (hinj : ∀ n,
      Set.InjOn (V (A := A) (n := n) hβγ.le) (P.Φ γ ((lt_add_one γ).trans hγ) n)) :
    P.StabilizesAt γ := by
  refine ⟨hγ, fun n φ hφ φ' hφ' hV ↦ ?_⟩
  have e1 := P.E_V_add_one_eq hβγ.le hγ hφ
  have e2 := P.E_V_add_one_eq hβγ.le hγ hφ'
  rw [V_eq_V_of_le (lt_add_one γ).le (add_one_le_of_lt hβγ) hV] at e1
  have hE : V hβγ.le '' E φ = V hβγ.le '' E φ' := e1.symm.trans e2
  have key : ∀ {x y : Ψ A (γ + 1) n}, x ∈ P.Φ (γ + 1) hγ n → y ∈ P.Φ (γ + 1) hγ n →
      V hβγ.le '' E x = V hβγ.le '' E y → E x ⊆ E y := by
    intro x y hx hy hxy ψ hψ
    obtain ⟨ψ', hψ', he⟩ : V hβγ.le ψ ∈ V hβγ.le '' E y := hxy ▸ ⟨ψ, hψ, rfl⟩
    rwa [hinj (n + 1) (P.E_subset γ hγ n x hx hψ) (P.E_subset γ hγ n y hy hψ') he.symm]
  exact Ψ.ext_succ hV ((key hφ hφ' hE).antisymm (key hφ' hφ hE.symm))

/-- **Proposition 5.5** (Larson, Scott processes): stabilization propagates upward.  If the
process stabilizes at `β`, `β ≤ γ` and `γ + 1 < δ`, then it stabilizes at `γ`. -/
theorem stabilizesAt_of_le {β γ : Ordinal.{0}} (hβ : P.StabilizesAt β) (hβγ : β ≤ γ)
    (hγ : γ + 1 < δ) : P.StabilizesAt γ := by
  induction γ using WellFoundedLT.induction with
  | _ γ ih =>
  rcases hβγ.eq_or_lt with rfl | hlt
  · exact hβ
  refine P.stabilizesAt_of_injOn_V hlt hγ fun n ↦
    P.injOn_V_of_forall_stabilizesAt hlt.le _ (fun η h1 h2 ↦ ih η h2 h1 ?_) n
  exact (add_one_le_of_lt h2).trans_lt ((lt_add_one γ).trans hγ)

/-! ### Rank (Definition 5.6) -/

/-- A Scott process is **terminating** (Larson, Definition 5.6) if it stabilizes at some
level. -/
def Terminating : Prop :=
  ∃ β, P.StabilizesAt β

/-- `β` is **the rank** of the process (Larson, Definition 5.6): the least level at which it
stabilizes. -/
def IsRank (β : Ordinal.{0}) : Prop :=
  IsLeast {γ | P.StabilizesAt γ} β

/-- The **rank** of a terminating Scott process (Larson, Definition 5.6): the least `β` such
that `V_{β,β+1}` is injective on `Φ_{β+1}`.  The rank of a nonterminating process is undefined,
so `rank` takes the proof of termination as an argument. -/
def rank (_h : P.Terminating) : Ordinal.{0} :=
  sInf {β | P.StabilizesAt β}

/-- `β` is the rank iff the process stabilizes at `β` and at no smaller level. -/
theorem isRank_iff {β : Ordinal.{0}} :
    P.IsRank β ↔ P.StabilizesAt β ∧ ∀ γ < β, ¬ P.StabilizesAt γ :=
  and_congr_right fun _ ↦
    ⟨fun h _ hγ hs ↦ (h hs).not_gt hγ, fun h _ hs ↦ not_lt.1 fun hlt ↦ h _ hlt hs⟩

/-- `rank` satisfies `IsRank`: it is the least stabilization level. -/
theorem isRank_rank (h : P.Terminating) : P.IsRank (P.rank h) :=
  isLeast_csInf h

/-- The rank is unique. -/
theorem IsRank.unique {P : ScottProcess A δ} {β γ : Ordinal.{0}} (hβ : P.IsRank β)
    (hγ : P.IsRank γ) : β = γ :=
  IsLeast.unique hβ hγ

/-- A process with rank `β` is terminating, and `rank` computes `β`. -/
theorem IsRank.rank_eq {P : ScottProcess A δ} {β : Ordinal.{0}} (hβ : P.IsRank β)
    (h : P.Terminating) : P.rank h = β :=
  (P.isRank_rank h).unique hβ

/-- The rank is at most every stabilization level. -/
theorem rank_le (h : P.Terminating) {γ : Ordinal.{0}} (hγ : P.StabilizesAt γ) :
    P.rank h ≤ γ :=
  (P.isRank_rank h).2 hγ

/-- By Proposition 5.5, the stabilization levels of a terminating process are exactly the
levels `γ` with `rank ≤ γ` and `γ + 1 < δ`. -/
theorem stabilizesAt_iff_rank_le (h : P.Terminating) {γ : Ordinal.{0}} :
    P.StabilizesAt γ ↔ P.rank h ≤ γ ∧ γ + 1 < δ :=
  ⟨fun hγ ↦ ⟨P.rank_le h hγ, hγ.1⟩,
    fun ⟨hle, hγ⟩ ↦ P.stabilizesAt_of_le (P.isRank_rank h).1 hle hγ⟩

/-! ### Remark 5.7 -/

/-- Injectivity of `V_{β,β+1}` on column `n`, including the length condition `β + 1 < δ`. -/
private def InjAt (β : Ordinal.{0}) (n : ℕ) : Prop :=
  ∃ h : β + 1 < δ, Set.InjOn (V (A := A) (n := n) (lt_add_one β).le) (P.Φ (β + 1) h n)

/-- Iterating Corollary 5.2 `k` times: injectivity at `β` on the columns `> n + k` gives
injectivity at `β + k` on the columns `> n`. -/
private theorem injAt_add_nat (n k : ℕ) (β : Ordinal.{0}) (hβ : β + k + 1 < δ)
    (h : ∀ m, n + k < m → P.InjAt β m) : ∀ m, n < m → P.InjAt (β + k) m := by
  induction k generalizing β with
  | zero =>
    intro m hm
    simpa using h m (by simpa using hm)
  | succ k ih =>
    intro m hm
    have e : β + 1 + (k : Ordinal.{0}) = β + ((k + 1 : ℕ) : Ordinal.{0}) := by
      rw [add_assoc, ← Nat.cast_one, ← Nat.cast_add, Nat.add_comm]
    have hβ' : β + 1 + k + 1 < δ := by rwa [e]
    have h2 : β + 1 + 1 < δ := by
      refine lt_of_le_of_lt ?_ hβ
      gcongr
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    have := ih (β + 1) hβ'
      (fun m hm ↦ ⟨h2, P.injOn_succ_of_injOn h2 (h (m + 1) (by omega)).2⟩) m hm
    rwa [e] at this

/-- **Remark 5.7** (Larson, Scott processes): if `β + n + 1 < δ` and `V_{β,β+1}` is injective
on `Φ^m_{β+1}` for every `m > n`, then the process stabilizes at `β + n`, so its rank is at most
`β + n` (`rank_le`).  Column `0` is handled by Proposition 3.5. -/
theorem stabilizesAt_add_nat {β : Ordinal.{0}} {n : ℕ} (hγ : β + n + 1 < δ)
    {hβ : β + 1 < δ}
    (h : ∀ m, n < m → Set.InjOn (V (A := A) (n := m) (lt_add_one β).le) (P.Φ (β + 1) hβ m)) :
    P.StabilizesAt (β + n) := by
  refine ⟨hγ, fun m ↦ ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact fun _ hx _ hy _ ↦ P.subsingleton_zero _ hγ hx hy
  · exact (P.injAt_add_nat 0 n β hγ (fun m hm ↦ ⟨hβ, h m (by simpa using hm)⟩) m hm).2

/-! ### Injectivity beyond a member of a level (Definition 5.8, Proposition 5.13) -/

/-- **Definition 5.8** (Larson, Scott processes): for `β + 1 < δ` and `φ ∈ Ψ^n_β`, the process
is **injective beyond `φ`** if for every `m`, every `j ∈ I_{n,m}` and every `ψ ∈ Φ^m_β` with
`φ = H^m_β(ψ, j)`, the fiber `V_{β,β+1}^{-1}[{ψ}] ∩ Φ_{β+1}` is a singleton. -/
def InjectiveBeyond {β : Ordinal.{0}} (hβ : β + 1 < δ) {n : ℕ} (φ : Ψ A β n) : Prop :=
  ∀ m (j : Fin n ↪ Fin m), ∀ ψ ∈ P.Φ β ((lt_add_one β).trans hβ) m, φ = H j ψ →
    ∃! x, x ∈ P.Φ (β + 1) hβ m ∧ V (lt_add_one β).le x = ψ

/-- The induction of Remark 5.9: if the process is injective beyond `φ ∈ Ψ^n_β`, then for every
level `η ∈ [β, δ)`, every `j ∈ I_{n,m}` and every `ψ ∈ Φ^m_β` with `φ = H^m_β(ψ, j)`, the fiber
`V_{β,η}^{-1}[{ψ}] ∩ Φ_η` is a subsingleton. -/
private theorem fiber_subsingleton_of_injectiveBeyond {β : Ordinal.{0}} (hβ : β + 1 < δ)
    {n : ℕ} {φ : Ψ A β n} (hinj : P.InjectiveBeyond hβ φ) {η : Ordinal.{0}} (hβη : β ≤ η)
    (hη : η < δ) {m : ℕ} (j : Fin n ↪ Fin m) {ψ : Ψ A β m}
    (hψ : ψ ∈ P.Φ β ((lt_add_one β).trans hβ) m) (hφψ : φ = H j ψ) :
    (P.fiber hβη hη ψ).Subsingleton := by
  rcases hβη.eq_or_lt with rfl | hlt
  · exact P.fiber_self_subsingleton _ _ _
  induction η using Ordinal.limitRecOn generalizing m with
  | zero => exact absurd hlt (not_lt.2 zero_le)
  | add_one η ih =>
    have hβη' : β ≤ η := lt_add_one_iff.1 hlt
    rcases hβη'.eq_or_lt with rfl | hlt'
    · exact fun x hx y hy ↦ (hinj m j ψ hψ hφψ).unique hx hy
    have hη' : η < δ := (lt_add_one η).trans hη
    have h1 : β + 1 ≤ η := add_one_le_of_lt hlt'
    have hV : ∀ {x y}, x ∈ P.fiber hβη hη ψ → y ∈ P.fiber hβη hη ψ →
        V (lt_add_one η).le x = V (lt_add_one η).le y := by
      rintro x y ⟨hx, hxψ⟩ ⟨hy, hyψ⟩
      refine ih hβη' hη' j hψ hφψ hlt' ⟨P.V_mem _ hη hx, ?_⟩ ⟨P.V_mem _ hη hy, ?_⟩
      · rwa [V_comp]
      · rwa [V_comp]
    have key : ∀ {x y}, x ∈ P.fiber hβη hη ψ → y ∈ P.fiber hβη hη ψ → E x ⊆ E y := by
      intro x y hxf hyf θ hθ
      have hxy0 := hV hxf hyf
      obtain ⟨hx, hxψ⟩ := hxf
      obtain ⟨hy, -⟩ := hyf
      have ex := P.E_V_add_one_eq hβη' hη hx
      have ey := P.E_V_add_one_eq hβη' hη hy
      obtain ⟨θ', hθ', he⟩ : V hβη' θ ∈ V hβη' '' E y := by
        rw [← ey, ← V_eq_V_of_le (lt_add_one η).le h1 hxy0, ex]
        exact ⟨θ, hθ, rfl⟩
      have hHθ : H (Fin.castLEEmb (Nat.le_succ m)) θ = V (lt_add_one η).le x := by
        rw [P.E_eq η hη m x hx] at hθ
        obtain ⟨ρ, ⟨-, hρ⟩, rfl⟩ := hθ
        rw [← V_H_comm, hρ]
      have hθβ : φ = H (j.trans (Fin.castLEEmb (Nat.le_succ m))) (V hβη' θ) := by
        rw [← H_comp, ← V_H_comm, hHθ, V_comp, hxψ, hφψ]
      have hθm := P.E_subset η hη m x hx hθ
      have hsub := ih hβη' hη' (j.trans (Fin.castLEEmb (Nat.le_succ m)))
        (P.V_mem hβη' hη' hθm) hθβ hlt'
      rw [hsub ⟨hθm, rfl⟩ ⟨P.E_subset η hη m y hy hθ', he⟩]
      exact hθ'
    intro x hx y hy
    exact Ψ.ext_succ (hV hx hy) ((key hx hy).antisymm (key hy hx))
  | limit η hηl ih =>
    rintro x ⟨hx, hxψ⟩ y ⟨hy, hyψ⟩
    refine Ψ.ext_limit hηl fun ζ hζ ↦ ?_
    rcases lt_or_ge β ζ with hβζ | hζβ
    · refine ih ζ hζ hβζ.le (hζ.trans hη) j hψ hφψ hβζ
        ⟨P.V_mem _ hη hx, ?_⟩ ⟨P.V_mem _ hη hy, ?_⟩
      · rwa [V_comp]
      · rwa [V_comp]
    · exact V_eq_V_of_le hβη hζβ (hxψ.trans hyψ.symm)

/-- The inductive claim in the proof of Proposition 5.13, at the level `η = β + p`: if
`θ ∈ Φ^k_η` is `H^c_η(ρ, i_k)` for some `ρ ∈ Φ^c_η` with `c = k + p` and
`V_{β,γ}^{-1}[{V_{β,η}(ρ)}] ∩ Φ_γ` a subsingleton, then `V_{η,γ}^{-1}[{θ}] ∩ Φ_γ` is a
subsingleton. -/
private theorem fiber_subsingleton_of_add_nat {β γ : Ordinal.{0}} (hγ : γ < δ) (p : ℕ) :
    ∀ (η : Ordinal.{0}) (_ : η = β + p) (hηγ : η ≤ γ) (k : ℕ) (θ : Ψ A η k)
      (_ : θ ∈ P.Φ η (hηγ.trans_lt hγ) k) (c : ℕ) (_ : c = k + p) (ρ : Ψ A η c)
      (_ : ρ ∈ P.Φ η (hηγ.trans_lt hγ) c) (hkc : k ≤ c) (hβη : β ≤ η)
      (_ : (P.fiber (hβη.trans hηγ) hγ (V hβη ρ)).Subsingleton)
      (_ : θ = H (Fin.castLEEmb hkc) ρ), (P.fiber hηγ hγ θ).Subsingleton := by
  induction p with
  | zero =>
    intro η hηe hηγ k θ hθ c hc ρ hρ hkc hβη hρ0 hθρ
    simp only [Nat.cast_zero, add_zero] at hηe
    subst hηe
    simp only [Nat.add_zero] at hc
    subst hc
    have e : Fin.castLEEmb hkc = Function.Embedding.refl (Fin c) :=
      Function.Embedding.ext fun i ↦ Fin.ext rfl
    rw [e, H_id] at hθρ
    subst hθρ
    rw [V_self] at hρ0
    exact hρ0
  | succ p ih =>
    intro η hηe hηγ k θ hθ c hc ρ hρ hkc hβη hρ0 hθρ
    have hηe' : η = β + p + 1 := by rw [hηe, Nat.cast_succ, add_assoc]
    subst hηe'
    have hη₀γ : β + p ≤ γ := (lt_add_one _).le.trans hηγ
    have hkc1 : k + 1 ≤ c := by omega
    have hlt : β + p + 1 < δ := hηγ.trans_lt hγ
    have hρ₁ : H (Fin.castLEEmb hkc1) ρ ∈ P.Φ (β + p + 1) hlt (k + 1) := by
      rw [P.image_H_eq _ _ (Fin.castLEEmb hkc1)]
      exact ⟨ρ, hρ, rfl⟩
    have hθ'E : V (lt_add_one (β + p)).le (H (Fin.castLEEmb hkc1) ρ) ∈ E θ := by
      rw [P.E_eq (β + p) hlt k θ hθ]
      refine ⟨_, ⟨hρ₁, ?_⟩, rfl⟩
      rw [H_comp, hθρ]
      rfl
    have hsub := ih (β + p) rfl hη₀γ (k + 1) _ (P.V_mem _ hlt hρ₁) c (by omega)
      (V (lt_add_one (β + p)).le ρ) (P.V_mem _ hlt hρ) hkc1 le_self_add
      (by rwa [V_comp]) (V_H_comm _ _ _)
    exact P.fiber_subsingleton_of_mem_E hηγ hγ hθ'E hsub

/-- **Proposition 5.13** (Larson, Scott processes): if `β + n + 1 < δ`, `φ ∈ Φ^n_β` and the
process is injective beyond `φ`, then the process stabilizes at `β + n`; hence its rank is at
most `β + n` (`rank_le`).  The proof `hβ : β + 1 < δ` in `InjectiveBeyond` is implicit: it is
determined by `hinj`. -/
theorem stabilizesAt_of_injectiveBeyond {β : Ordinal.{0}} {n : ℕ} (hγ : β + n + 1 < δ)
    {hβ : β + 1 < δ} {φ : Ψ A β n} (hφ : φ ∈ P.Φ β ((lt_add_one β).trans hβ) n)
    (hinj : P.InjectiveBeyond hβ φ) : P.StabilizesAt (β + n) := by
  have hβn : β ≤ β + n := le_self_add
  refine ⟨hγ, fun k ↦ ?_⟩
  rw [P.injOn_iff_fiber_subsingleton]
  intro θ hθ
  obtain ⟨φn, hφn, hφnφ⟩ := P.fiber_nonempty hβn ((lt_add_one _).trans hγ) hφ
  obtain ⟨ρ, hρ, j, hθρ, hφnρ⟩ := P.amalgamate (β + n) _ k n θ hθ φn hφn
  have hρ0 : (P.fiber (hβn.trans (lt_add_one _).le) hγ (V hβn ρ)).Subsingleton := by
    refine P.fiber_subsingleton_of_injectiveBeyond hβ hinj _ hγ j (P.V_mem hβn _ hρ) ?_
    rw [← V_H_comm, ← hφnρ, hφnφ]
  exact P.fiber_subsingleton_of_add_nat hγ n (β + n) rfl (lt_add_one _).le k θ hθ (k + n) rfl
    ρ hρ (Nat.le_add_right k n) hβn hρ0 hθρ

/-! ### The toy process -/

/-- `unitProcess` of length `δ` terminates iff `1 < δ`. -/
theorem unitProcess_terminating_iff {δ : Ordinal.{0}} (hδ : 0 < δ) :
    (unitProcess.{w} δ hδ).Terminating ↔ 1 < δ :=
  ⟨fun ⟨β, h, _⟩ ↦ lt_of_le_of_lt (by simp) h,
    fun h ↦ ⟨0, by simpa using h, fun _ x _ y _ _ ↦ Subsingleton.elim x y⟩⟩

/-- `unitProcess` of length `δ > 1` has rank `0`. -/
theorem unitProcess_isRank_zero {δ : Ordinal.{0}} (hδ : 0 < δ) (h1 : 1 < δ) :
    (unitProcess.{w} δ hδ).IsRank 0 :=
  ⟨⟨by simpa using h1, fun _ x _ y _ _ ↦ Subsingleton.elim x y⟩,
    fun _ _ ↦ zero_le⟩

/-- The rank of `unitProcess` is `0` (whenever it terminates, that is, when `1 < δ`). -/
theorem unitProcess_rank {δ : Ordinal.{0}} (hδ : 0 < δ) (h : (unitProcess.{w} δ hδ).Terminating) :
    (unitProcess.{w} δ hδ).rank h = 0 :=
  (unitProcess_isRank_zero hδ ((unitProcess_terminating_iff hδ).1 h)).rank_eq h

end ScottProcess

end InfinitaryLogic

end
