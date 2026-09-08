/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.OrbitRank

/-!
# Finite extension and the block back-and-forth hierarchy

Two conventions for symmetric back-and-forth with full atomic agreement at level `0`:

* `BFEquiv` (`Scott/BackAndForth.lean`): one element is added at each successor step.
* `BlockBFEquiv` (this module): for each `β < α`, a finite **block** of any length, zero
  included, is added at level `β` (Harrison-Trainor–Igusa–Knight, *Some new computable
  structures of high rank*, Definitions 1.1–1.2).

`BFEquiv` is unchanged.  Contents, in dependency order:

1. **Finite extension**: forth or back by a `k`-tuple costs `k` levels
   (`BFEquiv.forth_block`, `BFEquiv.back_block`).
2. `BlockBFEquiv`, with its public equation `blockBFEquiv_iff`, monotonicity, and the two
   comparison bounds `BlockBFEquiv.toBFEquiv` (block level `α` gives single-element level `α`)
   and `BFEquiv.toBlock` (single-element level `ω·α` gives block level `α`).
3. **Before any rank**: equivalence at every level is the same in both conventions
   (`bfEquiv_all_iff_blockBFEquiv_all`), so block stabilization reuses the orbit-rank machinery.
4. Block orbit rank and block Scott rank with the inequalities `r_B ≤ r ≤ ω·r_B` and
   `R_B ≤ R ≤ ω·R_B`, which need no closure hypothesis, and the transfer of strict bounds below
   `α` under the explicit hypothesis `∀ β < α, ω·β < α`, which is not implied by `α` being a
   countable limit and is not assumed anywhere.

The `K₂ ⊔ K₃` regression in `scripts/check_block_backandforth_regressions.lean` shows the two
hierarchies differ at the same level; it does not establish optimality of the `ω` factor.

Convention note: in the usual nonempty relational setting `BFEquiv` coincides with the Scott-rank
survey's symmetric hierarchy (arXiv:2011.03923, Definition 2.5).  On an empty carrier with
differing nullary facts they differ: `BFEquiv` retains the atomic condition explicitly at every
level, while the survey's positive clause consists solely of single-element moves.  The survey's
asymmetric Definition 2.1 tests only finitely many quantifier-free formulas at level `0`; that
finite-tested condition does not imply full atomic agreement (the other implication holds), and
no comparison with it is made here.
-/

namespace FirstOrder.Language

open Fin Ordinal

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} [L.Structure M] {N : Type w'} [L.Structure N]

/-! ### Finite extension -/

omit [L.IsRelational] in
/-- **Forth by a block**: a `k`-tuple can be matched at the cost of `k` levels. -/
theorem BFEquiv.forth_block {α : Ordinal} {n : ℕ} :
    ∀ (k : ℕ) {a : Fin n → M} {b : Fin n → N}, BFEquiv (L := L) (α + k) n a b →
      ∀ c : Fin k → M, ∃ d : Fin k → N,
        BFEquiv (L := L) α (n + k) (Fin.append a c) (Fin.append b d) := by
  intro k
  induction k generalizing α with
  | zero =>
    intro a b h c
    refine ⟨Fin.elim0, ?_⟩
    obtain rfl : c = Fin.elim0 := funext fun i => i.elim0
    have ha : Fin.append a (Fin.elim0 : Fin 0 → M) = a := funext fun i => by
      simp [Fin.append_elim0]
    have hb : Fin.append b (Fin.elim0 : Fin 0 → N) = b := funext fun i => by
      simp [Fin.append_elim0]
    rw [ha, hb]
    simpa using h
  | succ k ih =>
    intro a b h c
    -- `α + (k+1) = (α + 1) + k`: match the initial block at level `α + 1`, then one element
    have e : α + 1 + (k : Ordinal) = α + ((k + 1 : ℕ) : Ordinal) := by
      rw [add_assoc, Nat.cast_succ]
      congr 1
      rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, Nat.add_comm]
    have h'' : BFEquiv (L := L) ((α + 1) + k) n a b := by rwa [e]
    obtain ⟨d', hd'⟩ := ih h'' (Fin.init c)
    obtain ⟨d₀, hd₀⟩ := BFEquiv.forth (by rwa [Order.succ_eq_add_one] : BFEquiv (L := L)
      (Order.succ α) (n + k) (Fin.append a (Fin.init c)) (Fin.append b d')) (c (Fin.last k))
    refine ⟨Fin.snoc d' d₀, ?_⟩
    have hc : c = Fin.snoc (Fin.init c) (c (Fin.last k)) := (Fin.snoc_init_self c).symm
    rw [hc, Fin.append_snoc, Fin.append_snoc]
    exact hd₀

omit [L.IsRelational] in
/-- **Back by a block**: symmetric to `forth_block`. -/
theorem BFEquiv.back_block {α : Ordinal} {n : ℕ} (k : ℕ) {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) (α + k) n a b) (d : Fin k → N) :
    ∃ c : Fin k → M, BFEquiv (L := L) α (n + k) (Fin.append a c) (Fin.append b d) := by
  obtain ⟨c, hc⟩ := BFEquiv.forth_block (L := L) k (BFEquiv.symm h) d
  exact ⟨c, BFEquiv.symm hc⟩

/-! ### The block hierarchy -/

/-- The block back-and-forth relation (Harrison-Trainor–Igusa–Knight Definition 1.2): atomic
agreement, and for each `β < α` a forth and a back move by a finite block of any length at level
`β`.  Defined by well-founded recursion on `α`; use `blockBFEquiv_iff`. -/
noncomputable def BlockBFEquiv : Ordinal → ∀ n : ℕ, (Fin n → M) → (Fin n → N) → Prop :=
  Ordinal.lt_wf.fix fun α ih n a b =>
    SameAtomicType (L := L) a b ∧ ∀ β (hβ : β < α),
      (∀ (k : ℕ) (c : Fin k → M), ∃ d : Fin k → N,
        ih β hβ (n + k) (Fin.append a c) (Fin.append b d)) ∧
      (∀ (k : ℕ) (d : Fin k → N), ∃ c : Fin k → M,
        ih β hβ (n + k) (Fin.append a c) (Fin.append b d))

omit [L.IsRelational] in
/-- The public equation of `BlockBFEquiv`. -/
theorem blockBFEquiv_iff (α : Ordinal) {n : ℕ} (a : Fin n → M) (b : Fin n → N) :
    BlockBFEquiv (L := L) α n a b ↔
      SameAtomicType (L := L) a b ∧ ∀ β < α,
        (∀ (k : ℕ) (c : Fin k → M), ∃ d : Fin k → N,
          BlockBFEquiv (L := L) β (n + k) (Fin.append a c) (Fin.append b d)) ∧
        (∀ (k : ℕ) (d : Fin k → N), ∃ c : Fin k → M,
          BlockBFEquiv (L := L) β (n + k) (Fin.append a c) (Fin.append b d)) := by
  unfold BlockBFEquiv
  rw [WellFounded.fix_eq]

omit [L.IsRelational] in
theorem BlockBFEquiv.sameAtomicType {α : Ordinal} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : BlockBFEquiv (L := L) α n a b) : SameAtomicType (L := L) a b :=
  ((blockBFEquiv_iff α a b).mp h).1

omit [L.IsRelational] in
theorem BlockBFEquiv.forth {α β : Ordinal} (hβ : β < α) {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : BlockBFEquiv (L := L) α n a b) (k : ℕ) (c : Fin k → M) :
    ∃ d : Fin k → N, BlockBFEquiv (L := L) β (n + k) (Fin.append a c) (Fin.append b d) :=
  (((blockBFEquiv_iff α a b).mp h).2 β hβ).1 k c

omit [L.IsRelational] in
theorem BlockBFEquiv.back {α β : Ordinal} (hβ : β < α) {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : BlockBFEquiv (L := L) α n a b) (k : ℕ) (d : Fin k → N) :
    ∃ c : Fin k → M, BlockBFEquiv (L := L) β (n + k) (Fin.append a c) (Fin.append b d) :=
  (((blockBFEquiv_iff α a b).mp h).2 β hβ).2 k d

omit [L.IsRelational] in
/-- Level `0` is atomic agreement. -/
theorem blockBFEquiv_zero {n : ℕ} (a : Fin n → M) (b : Fin n → N) :
    BlockBFEquiv (L := L) 0 n a b ↔ SameAtomicType (L := L) a b := by
  rw [blockBFEquiv_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, fun β hβ => absurd hβ (not_lt_of_ge (_root_.zero_le))⟩⟩

omit [L.IsRelational] in
theorem BlockBFEquiv.monotone {α β : Ordinal} (hβα : β ≤ α) {n : ℕ} {a : Fin n → M}
    {b : Fin n → N} (h : BlockBFEquiv (L := L) α n a b) : BlockBFEquiv (L := L) β n a b := by
  rw [blockBFEquiv_iff] at h ⊢
  exact ⟨h.1, fun γ hγ => h.2 γ (lt_of_lt_of_le hγ hβα)⟩

omit [L.IsRelational] in
/-- **Block level `α` gives single-element level `α`**: a block of length one is a single move. -/
theorem BlockBFEquiv.toBFEquiv {α : Ordinal} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : BlockBFEquiv (L := L) α n a b) : BFEquiv (L := L) α n a b := by
  induction α using Ordinal.limitRecOn generalizing n a b with
  | zero => exact (BFEquiv.zero _ _).mpr h.sameAtomicType
  | add_one β ih =>
    rw [← Order.succ_eq_add_one, BFEquiv.succ]
    refine ⟨ih (h.monotone (Order.le_succ β)), fun m => ?_, fun n' => ?_⟩
    · obtain ⟨d, hd⟩ := h.forth (Order.lt_succ β) 1 ![m]
      refine ⟨d 0, ?_⟩
      have := ih hd
      rwa [Fin.append_right_eq_snoc, Fin.append_right_eq_snoc] at this
      -- `![m] 0 = m` definitionally
    · obtain ⟨c, hc⟩ := h.back (Order.lt_succ β) 1 ![n']
      refine ⟨c 0, ?_⟩
      have := ih hc
      rwa [Fin.append_right_eq_snoc, Fin.append_right_eq_snoc] at this
  | limit β hβ ih =>
    rw [BFEquiv.limit β hβ]
    exact fun γ hγ => ih γ hγ (h.monotone hγ.le)

omit [L.IsRelational] in
/-- The single-element level needed for a block move: `ω·β + k ≤ ω·α` when `β < α`. -/
private theorem omega_mul_add_nat_le {α β : Ordinal} (hβ : β < α) (k : ℕ) :
    Ordinal.omega0 * β + k ≤ Ordinal.omega0 * α :=
  calc Ordinal.omega0 * β + k ≤ Ordinal.omega0 * β + Ordinal.omega0 :=
        add_le_add_right (Ordinal.natCast_lt_omega0 k).le _
    _ = Ordinal.omega0 * Order.succ β := (Ordinal.mul_succ _ _).symm
    _ ≤ Ordinal.omega0 * α := mul_le_mul_right (Order.succ_le_of_lt hβ) _

omit [L.IsRelational] in
/-- Explicit-binder form of `BFEquiv.toBlock`, the shape the well-founded induction needs. -/
theorem BFEquiv.toBlock_aux (α : Ordinal) :
    ∀ (n : ℕ) (a : Fin n → M) (b : Fin n → N),
      BFEquiv (L := L) (Ordinal.omega0 * α) n a b → BlockBFEquiv (L := L) α n a b := by
  refine WellFoundedLT.induction
    (motive := fun α => ∀ (n : ℕ) (a : Fin n → M) (b : Fin n → N),
      BFEquiv (L := L) (Ordinal.omega0 * α) n a b → BlockBFEquiv (L := L) α n a b) α ?_
  intro α ih n a b h
  rw [blockBFEquiv_iff]
  refine ⟨(BFEquiv.zero _ _).mp (BFEquiv.monotone (_root_.zero_le) h),
    fun β hβ => ⟨fun k c => ?_, fun k d => ?_⟩⟩
  · obtain ⟨d, hd⟩ := BFEquiv.forth_block (L := L) k
      (BFEquiv.monotone (omega_mul_add_nat_le hβ k) h) c
    exact ⟨d, ih β hβ _ _ _ hd⟩
  · obtain ⟨c, hc⟩ := BFEquiv.back_block (L := L) k
      (BFEquiv.monotone (omega_mul_add_nat_le hβ k) h) d
    exact ⟨c, ih β hβ _ _ _ hc⟩

omit [L.IsRelational] in
/-- **Single-element level `ω·α` gives block level `α`**: a `k`-block at `β < α` is matched by
`forth_block` at level `ω·β + k ≤ ω·α`. -/
theorem BFEquiv.toBlock {α : Ordinal} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) (Ordinal.omega0 * α) n a b) : BlockBFEquiv (L := L) α n a b :=
  BFEquiv.toBlock_aux α n a b h

omit [L.IsRelational] in
/-- **Equivalence at every level is convention-independent.** -/
theorem bfEquiv_all_iff_blockBFEquiv_all {n : ℕ} {a : Fin n → M} {b : Fin n → N} :
    (∀ α : Ordinal.{uι}, BFEquiv (L := L) α n a b) ↔
      ∀ α : Ordinal.{uι}, BlockBFEquiv (L := L) α n a b :=
  ⟨fun h α => BFEquiv.toBlock (h (Ordinal.omega0 * α)), fun h α => (h α).toBFEquiv⟩

/-! ### Block orbit rank and block Scott rank -/

/-- The block stabilization set, all-levels form (Harrison-Trainor–Igusa–Knight Definition
1.3(1)). -/
def blockOrbitStable {n : ℕ} (a : Fin n → M) : Set Ordinal.{w} :=
  {α | ∀ b : Fin n → M, BlockBFEquiv (L := L) α n a b →
    ∀ γ : Ordinal.{w}, BlockBFEquiv (L := L) γ n a b}

omit [L.IsRelational] in
/-- The single-element orbit rank is a block stabilization level. -/
theorem orbitRank_mem_blockOrbitStable {n : ℕ} (a : Fin n → M) :
    orbitRank (L := L) a ∈ blockOrbitStable (L := L) a := fun _ hb =>
  bfEquiv_all_iff_blockBFEquiv_all.mp (bfEquiv_all_of_bfEquiv_orbitRank hb.toBFEquiv)

omit [L.IsRelational] in
theorem blockOrbitStable_nonempty {n : ℕ} (a : Fin n → M) :
    (blockOrbitStable (L := L) a).Nonempty :=
  ⟨_, orbitRank_mem_blockOrbitStable a⟩

/-- **Block orbit rank.** -/
noncomputable def blockOrbitRank {n : ℕ} (a : Fin n → M) : Ordinal.{w} :=
  sInf (blockOrbitStable (L := L) a)

omit [L.IsRelational] in
theorem blockOrbitRank_mem {n : ℕ} (a : Fin n → M) :
    blockOrbitRank (L := L) a ∈ blockOrbitStable (L := L) a :=
  csInf_mem (blockOrbitStable_nonempty a)

omit [L.IsRelational] in
theorem blockOrbitRank_le_of_mem {n : ℕ} {a : Fin n → M} {α : Ordinal.{w}}
    (h : α ∈ blockOrbitStable (L := L) a) : blockOrbitRank (L := L) a ≤ α :=
  csInf_le' h

omit [L.IsRelational] in
/-- `r_B ≤ r`. -/
theorem blockOrbitRank_le_orbitRank {n : ℕ} (a : Fin n → M) :
    blockOrbitRank (L := L) a ≤ orbitRank (L := L) a :=
  blockOrbitRank_le_of_mem (orbitRank_mem_blockOrbitStable a)

omit [L.IsRelational] in
/-- `r ≤ ω·r_B`. -/
theorem orbitRank_le_omega_mul_blockOrbitRank {n : ℕ} (a : Fin n → M) :
    orbitRank (L := L) a ≤ Ordinal.omega0 * blockOrbitRank (L := L) a := by
  apply orbitRank_le_of_mem
  intro b hb
  exact bfEquiv_all_iff_blockBFEquiv_all.mpr (blockOrbitRank_mem a b hb.toBlock)

/-- **Block Scott rank** `R_B = ⨆ (r_B(a) + 1)`. -/
noncomputable def blockScottRank (M : Type w) [L.Structure M] : Ordinal.{w} :=
  ⨆ x : (Σ n : ℕ, Fin n → M), blockOrbitRank (L := L) x.2 + 1

omit [L.IsRelational] in
theorem blockOrbitRank_add_one_le_blockScottRank {n : ℕ} (a : Fin n → M) :
    blockOrbitRank (L := L) a + 1 ≤ blockScottRank (L := L) M :=
  Ordinal.le_iSup (fun x : (Σ n : ℕ, Fin n → M) => blockOrbitRank (L := L) x.2 + 1) ⟨n, a⟩

omit [L.IsRelational] in
theorem blockScottRank_le {β : Ordinal.{w}}
    (h : ∀ (n : ℕ) (a : Fin n → M), blockOrbitRank (L := L) a + 1 ≤ β) :
    blockScottRank (L := L) M ≤ β :=
  Ordinal.iSup_le fun x => h x.1 x.2

omit [L.IsRelational] in
/-- `R_B ≤ R`. -/
theorem blockScottRank_le_internalScottRank :
    blockScottRank (L := L) M ≤ internalScottRank (L := L) M :=
  blockScottRank_le fun _ a =>
    (add_le_add_left (blockOrbitRank_le_orbitRank a) 1).trans
      (orbitRank_add_one_le_internalScottRank a)

omit [L.IsRelational] in
/-- `R ≤ ω·R_B`, via `r(a) + 1 ≤ ω·r_B(a) + 1 ≤ ω·(r_B(a) + 1) ≤ ω·R_B`. -/
theorem internalScottRank_le_omega_mul_blockScottRank :
    internalScottRank (L := L) M ≤ Ordinal.omega0 * blockScottRank (L := L) M := by
  refine internalScottRank_le fun n a => ?_
  calc orbitRank (L := L) a + 1
      ≤ Ordinal.omega0 * blockOrbitRank (L := L) a + 1 :=
        add_le_add_left (orbitRank_le_omega_mul_blockOrbitRank a) 1
    _ ≤ Ordinal.omega0 * blockOrbitRank (L := L) a + Ordinal.omega0 :=
        add_le_add_right Ordinal.one_lt_omega0.le _
    _ = Ordinal.omega0 * (blockOrbitRank (L := L) a + 1) := by
        rw [← Order.succ_eq_add_one, Ordinal.mul_succ]
    _ ≤ Ordinal.omega0 * blockScottRank (L := L) M :=
        mul_le_mul_right (blockOrbitRank_add_one_le_blockScottRank a) _

omit [L.IsRelational] in
/-- Strict bounds transfer downward for free. -/
theorem blockScottRank_lt_of_internalScottRank_lt {α : Ordinal.{w}}
    (h : internalScottRank (L := L) M < α) : blockScottRank (L := L) M < α :=
  lt_of_le_of_lt blockScottRank_le_internalScottRank h

omit [L.IsRelational] in
/-- Strict bounds transfer upward under the explicit closure hypothesis `∀ β < α, ω·β < α`.
This hypothesis is not implied by `α` being a countable limit (`ω·2`), and is not assumed
anywhere in this module. -/
theorem internalScottRank_lt_of_blockScottRank_lt {α : Ordinal.{w}}
    (hcl : ∀ β < α, Ordinal.omega0 * β < α) (h : blockScottRank (L := L) M < α) :
    internalScottRank (L := L) M < α :=
  lt_of_le_of_lt internalScottRank_le_omega_mul_blockScottRank (hcl _ h)

/-! ### Infinite pure sets -/

section PureSet

variable {X : Type w} [Infinite X]

local instance : Language.empty.Structure X := Language.emptyStructure

/-- Every tuple of an infinite pure set has block orbit rank `0`. -/
theorem blockOrbitRank_pureSet {n : ℕ} (a : Fin n → X) :
    blockOrbitRank (L := Language.empty) (M := X) a = 0 := by
  apply le_antisymm _ (_root_.zero_le)
  apply blockOrbitRank_le_of_mem
  intro b hb
  exact bfEquiv_all_iff_blockBFEquiv_all.mp (bfEquiv_all_of_pattern a b
    ((sameAtomicType_empty_iff a b).mp ((blockBFEquiv_zero _ _).mp hb)))

/-- An infinite pure set has block Scott rank `1`. -/
theorem blockScottRank_pureSet : blockScottRank (L := Language.empty) X = 1 := by
  apply le_antisymm
  · exact blockScottRank_le fun n a => by rw [blockOrbitRank_pureSet]; simp
  · have := blockOrbitRank_add_one_le_blockScottRank (L := Language.empty) (M := X) Fin.elim0
    rwa [blockOrbitRank_pureSet, zero_add] at this

end PureSet

end FirstOrder.Language
