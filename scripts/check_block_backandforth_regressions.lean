/-
Regression guard for finite extension and the block back-and-forth hierarchy
(`Scott/BlockBackAndForth.lean`).

Acceptance tests: `forth_block` at `k = 0` (free) and `k = 1` (a single move); the two
comparison bounds and the convention-independence of equivalence at every level; the rank
inequalities `r_B ≤ r ≤ ω·r_B` and `R_B ≤ R ≤ ω·R_B` without a closure hypothesis, and the
strict-bound transfer under the explicit hypothesis; `K₂ ⊔ K₃`: single-element level `1` holds
between a `K₂`-vertex and a `K₃`-vertex while block level `1` fails, which shows the hierarchies
differ at the same level (it does not establish optimality of the `ω` factor); the infinite pure
set has block orbit rank `0` and block Scott rank `1`.  `BFEquiv` is unchanged.  Headline
declarations use only the standard axioms.

Run with: lake env lean scripts/check_block_backandforth_regressions.lean
-/
import InfinitaryLogic.Scott.BlockBackAndForth
import Mathlib.Tactic.FinCases

open Lean FirstOrder Language

variable {L : Language.{u, v}} [L.IsRelational] {M : Type w} [L.Structure M]
  {N : Type w'} [L.Structure N]

omit [L.IsRelational] in
/-- `k = 0`: no level is spent. -/
theorem forth_block_zero_regression {α : Ordinal} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) α n a b) (c : Fin 0 → M) :
    ∃ d : Fin 0 → N, BFEquiv (L := L) α (n + 0) (Fin.append a c) (Fin.append b d) :=
  BFEquiv.forth_block 0 (by simpa using h) c

omit [L.IsRelational] in
/-- `k = 1`: one level, as in `BFEquiv.forth`. -/
theorem forth_block_one_regression {α : Ordinal} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) (Order.succ α) n a b) (m : M) :
    ∃ d : Fin 1 → N, BFEquiv (L := L) α (n + 1) (Fin.append a ![m]) (Fin.append b d) :=
  BFEquiv.forth_block 1 (by simpa [Order.succ_eq_add_one] using h) ![m]

omit [L.IsRelational] in
/-- Both comparison bounds and the all-levels equivalence. -/
theorem comparison_regression {α : Ordinal} {n : ℕ} {a : Fin n → M} {b : Fin n → N} :
    (BlockBFEquiv (L := L) α n a b → BFEquiv (L := L) α n a b) ∧
    (BFEquiv (L := L) (Ordinal.omega0 * α) n a b → BlockBFEquiv (L := L) α n a b) ∧
    ((∀ γ : Ordinal.{w}, BFEquiv (L := L) γ n a b) ↔ ∀ γ : Ordinal.{w}, BlockBFEquiv (L := L) γ n a b) :=
  ⟨BlockBFEquiv.toBFEquiv, BFEquiv.toBlock, bfEquiv_all_iff_blockBFEquiv_all⟩

omit [L.IsRelational] in
/-- The rank inequalities, with no closure hypothesis. -/
theorem rank_inequalities_regression {n : ℕ} (a : Fin n → M) :
    blockOrbitRank (L := L) a ≤ orbitRank (L := L) a ∧
    orbitRank (L := L) a ≤ Ordinal.omega0 * blockOrbitRank (L := L) a ∧
    blockScottRank (L := L) M ≤ internalScottRank (L := L) M ∧
    internalScottRank (L := L) M ≤ Ordinal.omega0 * blockScottRank (L := L) M :=
  ⟨blockOrbitRank_le_orbitRank a, orbitRank_le_omega_mul_blockOrbitRank a,
    blockScottRank_le_internalScottRank, internalScottRank_le_omega_mul_blockScottRank⟩

omit [L.IsRelational] in
/-- Strict bounds: free downward, upward only under the explicit closure hypothesis. -/
theorem strict_transfer_regression {α : Ordinal.{w}} (hcl : ∀ β < α, Ordinal.omega0 * β < α) :
    (internalScottRank (L := L) M < α → blockScottRank (L := L) M < α) ∧
    (blockScottRank (L := L) M < α → internalScottRank (L := L) M < α) :=
  ⟨blockScottRank_lt_of_internalScottRank_lt, internalScottRank_lt_of_blockScottRank_lt hcl⟩

/-! ### The graph `K₂ ⊔ K₃` -/

section Graph

/-- The one-symbol graph language. -/
inductive GSym : ℕ → Type
  | adj : GSym 2

/-- The graph language: one binary relation, no functions. -/
def graphLang : Language := ⟨fun _ => Empty, GSym⟩

instance : graphLang.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

/-- Adjacency of `K₂ ⊔ K₃` on `Fin 5`. -/
def adjK : Fin 5 → Fin 5 → Bool
  | 0, 1 | 1, 0 => true
  | 2, 3 | 3, 2 | 2, 4 | 4, 2 | 3, 4 | 4, 3 => true
  | _, _ => false

/-- The structure `K₂ ⊔ K₃`. -/
instance instGraphK : graphLang.Structure (Fin 5) where
  funMap f _ := (f : Empty).elim
  RelMap {n} R v := match n, R with
    | _, GSym.adj => adjK (v 0) (v 1) = true

instance decRelMapK {n : ℕ} (R : graphLang.Relations n) (v : Fin n → Fin 5) :
    Decidable (Structure.RelMap R v) := by
  cases R
  exact inferInstanceAs (Decidable (adjK (v 0) (v 1) = true))

/-- Atomic agreement, read off through the equality and adjacency atoms. -/
theorem sameAtomicType_K {n : ℕ} (a b : Fin n → Fin 5)
    (heq : ∀ i j : Fin n, a i = a j ↔ b i = b j)
    (hrel : ∀ f : Fin 2 → Fin n, adjK (a (f 0)) (a (f 1)) = true ↔ adjK (b (f 0)) (b (f 1)) = true) :
    SameAtomicType (L := graphLang) (M := Fin 5) (N := Fin 5) a b := by
  intro idx
  cases idx with
  | eq i j => exact heq i j
  | rel R f =>
    cases R
    exact hrel f

/-- Atomic agreement gives the adjacency atoms. -/
theorem adj_of_sameAtomicType_K {n : ℕ} {a b : Fin n → Fin 5}
    (h : SameAtomicType (L := graphLang) (M := Fin 5) (N := Fin 5) a b) (i j : Fin n) :
    adjK (a i) (a j) = true ↔ adjK (b i) (b j) = true :=
  h (AtomicIdx.rel GSym.adj ![i, j])

/-- Atomic agreement gives the equality atoms. -/
theorem eq_of_sameAtomicType_K {n : ℕ} {a b : Fin n → Fin 5}
    (h : SameAtomicType (L := graphLang) (M := Fin 5) (N := Fin 5) a b) (i j : Fin n) :
    a i = a j ↔ b i = b j :=
  h (AtomicIdx.eq i j)

/-- Vertices `0 ∈ K₂` and `2 ∈ K₃` are equivalent at single-element level `1` (as in the
orbit-rank guard). -/
theorem bfEquiv_one_K : BFEquiv (L := graphLang) (M := Fin 5) (N := Fin 5) 1 1 ![0] ![2] := by
  rw [show (1 : Ordinal) = Order.succ 0 by simp, BFEquiv.succ]
  refine ⟨(BFEquiv.zero _ _).mpr (sameAtomicType_K _ _ (by decide) (by decide)), ?_, ?_⟩
  · intro m
    have : ∃ n' : Fin 5, SameAtomicType (L := graphLang) (M := Fin 5) (N := Fin 5)
        (Fin.snoc ![0] m) (Fin.snoc ![2] n') := by
      fin_cases m
      · exact ⟨2, sameAtomicType_K _ _ (by decide) (by decide)⟩
      · exact ⟨3, sameAtomicType_K _ _ (by decide) (by decide)⟩
      · exact ⟨0, sameAtomicType_K _ _ (by decide) (by decide)⟩
      · exact ⟨0, sameAtomicType_K _ _ (by decide) (by decide)⟩
      · exact ⟨0, sameAtomicType_K _ _ (by decide) (by decide)⟩
    obtain ⟨n', hn'⟩ := this
    exact ⟨n', (BFEquiv.zero _ _).mpr hn'⟩
  · intro n'
    have : ∃ m : Fin 5, SameAtomicType (L := graphLang) (M := Fin 5) (N := Fin 5)
        (Fin.snoc ![0] m) (Fin.snoc ![2] n') := by
      fin_cases n'
      · exact ⟨2, sameAtomicType_K _ _ (by decide) (by decide)⟩
      · exact ⟨2, sameAtomicType_K _ _ (by decide) (by decide)⟩
      · exact ⟨0, sameAtomicType_K _ _ (by decide) (by decide)⟩
      · exact ⟨1, sameAtomicType_K _ _ (by decide) (by decide)⟩
      · exact ⟨1, sameAtomicType_K _ _ (by decide) (by decide)⟩
    obtain ⟨m, hm⟩ := this
    exact ⟨m, (BFEquiv.zero _ _).mpr hm⟩

/-- **Block level `1` fails**: the 2-block `[3, 4]` of the two mutually adjacent neighbours of
`2` cannot be matched from `0`, which has one neighbour. -/
theorem not_blockBFEquiv_one_K :
    ¬ BlockBFEquiv (L := graphLang) (M := Fin 5) (N := Fin 5) 1 1 ![0] ![2] := by
  intro h
  obtain ⟨c, hc⟩ := h.back (zero_lt_one) 2 ![3, 4]
  have h0 := (blockBFEquiv_zero _ _).mp hc
  -- positions: `0 ↦ 0`, `1 ↦ c 0`, `2 ↦ c 1` on the left; `0 ↦ 2`, `1 ↦ 3`, `2 ↦ 4` on the right
  have e1 : Fin.append ![(0 : Fin 5)] c 1 = c 0 := rfl
  have e2 : Fin.append ![(0 : Fin 5)] c 2 = c 1 := rfl
  have e0 : Fin.append ![(0 : Fin 5)] c 0 = 0 := rfl
  have f0 : Fin.append ![(2 : Fin 5)] ![3, 4] 0 = 2 := rfl
  have f1 : Fin.append ![(2 : Fin 5)] ![3, 4] 1 = 3 := rfl
  have f2 : Fin.append ![(2 : Fin 5)] ![3, 4] 2 = 4 := rfl
  have h01 := adj_of_sameAtomicType_K h0 0 1
  have h02 := adj_of_sameAtomicType_K h0 0 2
  have h12 := eq_of_sameAtomicType_K h0 1 2
  rw [e0, e1, f0, f1] at h01
  rw [e0, e2, f0, f2] at h02
  rw [e1, e2, f1, f2] at h12
  have hc0 : adjK 0 (c 0) = true := h01.mpr (by decide)
  have hc1 : adjK 0 (c 1) = true := h02.mpr (by decide)
  have hne : c 0 ≠ c 1 := fun e => absurd (h12.mp e) (by decide)
  have hone : ∀ y : Fin 5, adjK 0 y = true → y = 1 := by decide
  exact hne ((hone _ hc0).trans (hone _ hc1).symm)

end Graph

section PureSet

local instance : Language.empty.Structure ℕ := Language.emptyStructure

theorem pureSet_block_regression :
    blockOrbitRank (L := Language.empty) (M := ℕ) ![3, 3] = 0 ∧
    blockScottRank (L := Language.empty) ℕ = 1 :=
  ⟨blockOrbitRank_pureSet _, blockScottRank_pureSet⟩

end PureSet

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.BFEquiv.forth_block, `FirstOrder.Language.BFEquiv.back_block,
   `FirstOrder.Language.blockBFEquiv_iff, `FirstOrder.Language.BlockBFEquiv.monotone,
   `FirstOrder.Language.BlockBFEquiv.toBFEquiv, `FirstOrder.Language.BFEquiv.toBlock,
   `FirstOrder.Language.bfEquiv_all_iff_blockBFEquiv_all,
   `FirstOrder.Language.blockOrbitRank_le_orbitRank,
   `FirstOrder.Language.orbitRank_le_omega_mul_blockOrbitRank,
   `FirstOrder.Language.blockScottRank_le_internalScottRank,
   `FirstOrder.Language.internalScottRank_le_omega_mul_blockScottRank,
   `FirstOrder.Language.internalScottRank_lt_of_blockScottRank_lt,
   `FirstOrder.Language.blockOrbitRank_pureSet, `FirstOrder.Language.blockScottRank_pureSet,
   `forth_block_zero_regression, `forth_block_one_regression, `comparison_regression,
   `rank_inequalities_regression, `strict_transfer_regression, `bfEquiv_one_K,
   `not_blockBFEquiv_one_K, `pureSet_block_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "block back-and-forth regression guard: OK (finite extension at k = 0 and 1, both \
    comparison bounds, all-levels convention independence, rank inequalities without closure, \
    strict transfer under the explicit hypothesis, K2+K3 single level 1 holds while block level 1 \
    fails, infinite pure set; headline declarations on standard axioms)"
