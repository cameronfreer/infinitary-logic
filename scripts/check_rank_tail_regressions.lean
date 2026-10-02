/-
Regression guard for the rank tails, the extracted `ℵ₁` upper bound and the least level of a
cover (`InfinitaryLogic/OrdinalCountability.lean`).

Every public theorem is *applied*, not only listed for its axioms.

* **A countable type: `ℕ` with the zero rank.**  The tail lemmas on concrete values (the tail at
  `0` is `univ`, the tail at `1` is empty, the loss at `0` is everything, continuity at the
  prelimit `0` and the limit `ω`), countable complements and losses, no persistent core, empty
  tails from `ω₁` on, `#ℕ ≤ ℵ₁`, and **negative**: the nonempty losses are not cofinal below `ω₁`.
* **An uncountable type: the countable ordinals `Set.Iio ω₁` ranked by their value.**  The fibres
  are singletons, hence countable; the type is uncountable (a bound `β` on all ranks is itself a
  rank); the nonempty losses are cofinal below `ω₁`; and `#(Set.Iio ω₁) = ℵ₁` both through
  `mk_eq_aleph_one_of_countable_fibres` and through `mk_eq_aleph_one_of_domains` on the tails
  (the unchanged statement, still applied), whose upper half `mk_le_aleph_one_of_domains` is
  applied on its own.
* **The empty type.**  Every tail is empty, the persistent core is empty, `#Empty ≤ ℵ₁`, the
  losses are not cofinal, and the empty family covers `Empty`.
* **An overlapping cover of `Bool`**: `Q 0 = {true}` and `Q α = univ` for `α ≥ 1`.  The least
  level picks the least index (`true ↦ 0`, `false ↦ 1`, though `false ∈ Q 2` as well); its fibres
  are countable, its tails are the complements of the initial unions (the tail at `1` is
  `{false}`), and composed with `mk_le_aleph_one_of_countable_fibres` it bounds `#Bool`.
* **The covering hypothesis is necessary** for `rankTail_leastLevel`: for `Q α = {true}` on
  `Bool`, the point `false` lies in no `Q α`, so `leastLevel Q false = sInf ∅ = 0`, and at `η = 1`
  the identity fails (`false` is in the complement of `Q 0` but not in the tail at `1`).
* **Import closure** of the module: the only project module it reaches is `OrdinalUtil`, and no
  Scott, Scott-process, descriptive, model-theory, Karp, `Lω₁ω`, admissible, method, conditional
  or work-in-progress module.

All public declarations of the module and of this guard use only the standard axioms.

Run with: lake env lean scripts/check_rank_tail_regressions.lean
-/
import InfinitaryLogic.OrdinalCountability

open Lean InfinitaryLogic Set

noncomputable section

namespace RankTailGuard

/-- `1 < ω₁`, used for concrete levels. -/
theorem one_lt_omega1 : (1 : Ordinal.{0}) < Ordinal.omega 1 := by
  rw [Cardinal.lt_omega_iff_card_lt, Ordinal.card_one]
  exact Cardinal.one_lt_aleph0.trans Cardinal.aleph0_lt_aleph_one

/-- `ω < ω₁`. -/
theorem omega0_lt_omega1 : Ordinal.omega0 < Ordinal.omega 1 := by
  rw [← Ordinal.omega_zero]
  exact Ordinal.omega_lt_omega.2 zero_lt_one

/-! ### A countable type: `ℕ` with the zero rank -/

section Nat

/-- The zero rank on `ℕ`. -/
def r0 : ℕ → Ordinal.{0} := fun _ ↦ 0

theorem r0_lt (n : ℕ) : r0 n < Ordinal.omega 1 := Ordinal.omega_pos 1

theorem r0_fib : ∀ α < Ordinal.omega 1, Countable {n // r0 n = α} := fun _ _ ↦ inferInstance

/-- The unconditional tail lemmas on concrete values. -/
theorem nat_tails :
    rankTail r0 0 = univ ∧ rankTail r0 1 = ∅ ∧ (rankTail r0 1)ᶜ = univ ∧
      rankTail r0 0 \ rankTail r0 (Order.succ 0) = univ ∧
      rankTail r0 0 = ⋂ η < (0 : Ordinal.{0}), rankTail r0 η ∧
      rankTail r0 Ordinal.omega0 = ⋂ η < Ordinal.omega0, rankTail r0 η ∧
      rankTail r0 1 ⊆ rankTail r0 0 := by
  have h1 : rankTail r0 1 = ∅ := by
    rw [← compl_univ, ← rankTail_zero r0, compl_rankTail]
    ext n
    simp [rankTail, r0]
  refine ⟨rankTail_zero r0, h1, by rw [h1, compl_empty], ?_,
    rankTail_eq_iInter_of_isSuccPrelimit r0 Ordinal.isSuccPrelimit_zero,
    rankTail_iInter r0 _ Ordinal.isSuccLimit_omega0, rankTail_antitone r0 zero_le_one⟩
  rw [rankTail_diff_succ]
  exact eq_univ_of_forall fun _ ↦ rfl

/-- The conditional tail lemmas, applied. -/
theorem nat_conditional :
    (rankTail r0 1)ᶜ.Countable ∧ (rankTail r0 0 \ rankTail r0 (Order.succ 0)).Countable ∧
      (⋂ η < Ordinal.omega 1, rankTail r0 η) = ∅ ∧ rankTail r0 (Ordinal.omega 1) = ∅ ∧
      Cardinal.mk ℕ ≤ Cardinal.aleph 1 :=
  ⟨rankTail_compl_countable r0 r0_fib one_lt_omega1, rankTail_loss_countable r0 r0_lt r0_fib 0,
    rankTail_persistent_eq_empty r0 r0_lt, rankTail_eq_empty_of_omega_one_le r0 r0_lt le_rfl,
    mk_le_aleph_one_of_countable_fibres r0 r0_lt r0_fib⟩

/-- **Negative**: on the countable `ℕ` the nonempty losses are not cofinal below `ω₁`. -/
theorem nat_not_cofinal :
    ¬ ∀ γ < Ordinal.omega 1, ∃ η, γ ≤ η ∧ η < Ordinal.omega 1 ∧
      (rankTail r0 η \ rankTail r0 (Order.succ η)).Nonempty :=
  fun h ↦ (rankTail_cofinal_losses_iff r0 r0_lt r0_fib).1 h inferInstance

end Nat

/-! ### An uncountable type: the countable ordinals ranked by their value -/

section Omega1

/-- The countable ordinals, a type in `Type 1`. -/
abbrev W : Type 1 := Set.Iio (Ordinal.omega.{0} 1)

/-- The rank of a countable ordinal is its value. -/
def rv : W → Ordinal.{0} := Subtype.val

theorem rv_lt (x : W) : rv x < Ordinal.omega 1 := x.2

/-- **The fibres are singletons.** -/
theorem rv_fibre {α : Ordinal.{0}} (hα : α < Ordinal.omega 1) :
    {x : W | rv x = α} = {⟨α, hα⟩} := by
  ext x
  simp only [mem_ofPred_eq, mem_singleton_iff]
  exact ⟨fun h ↦ Subtype.ext h, fun h ↦ h ▸ rfl⟩

theorem rv_fib : ∀ α < Ordinal.omega 1, Countable {x : W // rv x = α} := fun α hα ↦ by
  have := (rv_fibre hα ▸ countable_singleton (⟨α, hα⟩ : W) : {x : W | rv x = α}.Countable)
  exact this.to_subtype

/-- **The countable ordinals are uncountable**: a bound `β < ω₁` on every rank is itself a rank. -/
theorem W_not_countable : ¬ Countable W := fun hW ↦ by
  obtain ⟨β, hβ, hb⟩ := (countable_iff_rank_bounded rv rv_lt rv_fib univ).1 countable_univ
  exact lt_irrefl β (hb ⟨β, hβ⟩ (mem_univ _))

/-- **Cofinal losses** on the uncountable type. -/
theorem W_cofinal : ∀ γ < Ordinal.omega 1, ∃ η, γ ≤ η ∧ η < Ordinal.omega 1 ∧
    (rankTail rv η \ rankTail rv (Order.succ η)).Nonempty :=
  (rankTail_cofinal_losses_iff rv rv_lt rv_fib).2 W_not_countable

/-- **`#W = ℵ₁`** from countable fibres. -/
theorem W_mk : Cardinal.mk W = Cardinal.aleph 1 :=
  mk_eq_aleph_one_of_countable_fibres rv rv_lt rv_fib W_not_countable

/-- Every point leaves the tail just above its rank. -/
theorem W_leave (x : W) : ∃ β, β < Ordinal.omega 1 ∧ x ∉ rankTail rv β :=
  ⟨Order.succ (rv x), (Cardinal.isSuccLimit_omega 1).succ_lt (rv_lt x),
    (Order.lt_succ (rv x)).not_ge⟩

/-- **The extracted upper half**, applied on its own (no monotonicity or nonemptiness). -/
theorem W_mk_le : Cardinal.mk W ≤ Cardinal.aleph 1 :=
  mk_le_aleph_one_of_domains (rankTail rv) (fun _ hβ ↦ rankTail_compl_countable rv rv_fib hβ)
    W_leave

/-- **`#W = ℵ₁` through `mk_eq_aleph_one_of_domains`**, the unchanged statement: every tail below
`ω₁` is nonempty, since it contains its own level. -/
theorem W_mk_domains : Cardinal.mk W = Cardinal.aleph 1 :=
  mk_eq_aleph_one_of_domains (rankTail rv) (rankTail_antitone rv)
    (fun _ hβ ↦ rankTail_compl_countable rv rv_fib hβ)
    (fun β hβ ↦ ⟨⟨β, hβ⟩, show β ≤ β from le_rfl⟩) W_leave

end Omega1

/-! ### The empty type -/

section EmptyType

/-- The (unique) rank on `Empty`. -/
def re : Empty → Ordinal.{0} := Empty.elim

theorem re_lt (x : Empty) : re x < Ordinal.omega 1 := x.elim

theorem re_fib : ∀ α < Ordinal.omega 1, Countable {x : Empty // re x = α} :=
  fun _ _ ↦ inferInstance

/-- On the empty type: empty tails and persistent core, `#Empty ≤ ℵ₁`, no cofinal losses, and a
trivially covering family with countable least-level fibres. -/
theorem empty_case :
    rankTail re 0 = ∅ ∧ (⋂ η < Ordinal.omega 1, rankTail re η) = ∅ ∧
      Cardinal.mk Empty ≤ Cardinal.aleph 1 ∧
      ¬ (∀ γ < Ordinal.omega 1, ∃ η, γ ≤ η ∧ η < Ordinal.omega 1 ∧
        (rankTail re η \ rankTail re (Order.succ η)).Nonempty) ∧
      (∀ α < Ordinal.omega 1,
        Countable {x : Empty // leastLevel (fun _ ↦ (∅ : Set Empty)) x = α}) :=
  ⟨eq_empty_of_isEmpty _, rankTail_persistent_eq_empty re re_lt,
    mk_le_aleph_one_of_countable_fibres re re_lt re_fib,
    fun h ↦ (rankTail_cofinal_losses_iff re re_lt re_fib).1 h inferInstance,
    countable_fibres_leastLevel _ (eq_univ_of_forall fun x ↦ x.elim) fun _ _ ↦ countable_empty⟩

end EmptyType

/-! ### An overlapping cover of `Bool` -/

section Cover

/-- `Q 0 = {true}` and `Q α = univ` for `α ≥ 1`: the members overlap. -/
def Qb (α : Ordinal.{0}) : Set Bool := if α = 0 then {true} else univ

theorem Qb_cover : (⋃ α < Ordinal.omega 1, Qb α) = univ :=
  eq_univ_of_forall fun b ↦ mem_iUnion₂.2 ⟨1, one_lt_omega1, by simp [Qb]⟩

/-- **The least level picks the least index**: `true` is first covered at `0`, `false` at `1`,
although `false` also lies in `Q 2`. -/
theorem Qb_levels : leastLevel Qb true = 0 ∧ leastLevel Qb false = 1 ∧ false ∈ Qb 2 := by
  have hmem := leastLevel_mem Qb Qb_cover false
  refine ⟨?_, le_antisymm ?_ ?_, by simp [Qb]⟩
  · exact le_antisymm (csInf_le' (s := {α | true ∈ Qb α}) (by simp [Qb])) zero_le
  · exact csInf_le' (s := {α | false ∈ Qb α}) (by simp [Qb])
  · rw [Order.one_le_iff_pos, pos_iff_ne_zero]
    intro h
    rw [h] at hmem
    simp [Qb] at hmem

/-- The cover lemmas, applied: levels below `ω₁`, fibres inside the members and countable, the
tail at `1` is `{false}`, and the composite bound `#Bool ≤ ℵ₁`. -/
theorem Qb_applied :
    leastLevel Qb false < Ordinal.omega 1 ∧
      {b | leastLevel Qb b = 0} ⊆ Qb 0 ∧
      rankTail (leastLevel Qb) 1 = {false} ∧
      Cardinal.mk Bool ≤ Cardinal.aleph 1 := by
  have hfib := countable_fibres_leastLevel Qb Qb_cover fun _ _ ↦ to_countable _
  refine ⟨leastLevel_lt_omega1 Qb Qb_cover false, setOf_leastLevel_eq_subset Qb Qb_cover 0, ?_,
    mk_le_aleph_one_of_countable_fibres _ (leastLevel_lt_omega1 Qb Qb_cover) hfib⟩
  rw [rankTail_leastLevel Qb Qb_cover]
  ext b
  cases b <;> simp [Qb]

end Cover

/-! ### The covering hypothesis is necessary -/

section Uncovered

/-- `Q α = {true}` for every `α`: the point `false` lies in no member. -/
def Qt (_ : Ordinal.{0}) : Set Bool := {true}

/-- **Negative**: without the covering hypothesis, `leastLevel Qt false = sInf ∅ = 0`, and the
tail identity fails at `η = 1`. -/
theorem uncovered_fails :
    (⋃ α < Ordinal.omega 1, Qt α) ≠ univ ∧ leastLevel Qt false = 0 ∧
      rankTail (leastLevel Qt) 1 ≠ (⋃ α < (1 : Ordinal.{0}), Qt α)ᶜ := by
  have h0 : leastLevel Qt false = 0 := by
    have : {α : Ordinal.{0} | false ∈ Qt α} = ∅ := by ext; simp [Qt]
    rw [leastLevel, this, Ordinal.sInf_empty]
  refine ⟨fun h ↦ ?_, h0, fun h ↦ ?_⟩
  · have := h ▸ mem_univ false
    simp [Qt] at this
  · have hf : false ∈ (⋃ α < (1 : Ordinal.{0}), Qt α)ᶜ := by simp [Qt]
    rw [← h] at hf
    exact absurd (h0 ▸ hf : (1 : Ordinal.{0}) ≤ 0) (not_le.2 zero_lt_one)

end Uncovered

end RankTailGuard

/-! ### Import closure and axiom audit -/

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

/-- Module-name prefixes no module of the closure may have. -/
def forbiddenPrefixes : List Name :=
  [`InfinitaryLogic.Scott, `InfinitaryLogic.ScottProcess, `InfinitaryLogic.Descriptive,
   `InfinitaryLogic.ModelTheory, `InfinitaryLogic.Karp, `InfinitaryLogic.Lomega1omega,
   `InfinitaryLogic.Admissible, `InfinitaryLogic.Methods, `InfinitaryLogic.Conditional,
   `InfinitaryLogic.WIP]

/-- The only project modules the closure may contain. -/
def allowedProject : List Name :=
  [`InfinitaryLogic.OrdinalCountability, `InfinitaryLogic.OrdinalUtil]

run_cmd do
  let env ← getEnv
  let target := `InfinitaryLogic.OrdinalCountability
  unless (env.getModuleIdx? target).isSome do
    throwError "module {target} is not in the environment"
  let cl := importClosure env target
  unless cl.contains `InfinitaryLogic.OrdinalUtil do
    throwError "[MISSING ROUTE] InfinitaryLogic.OrdinalUtil is not in the closure of {target}"
  let hits := cl.toList.filter fun m ↦ forbiddenPrefixes.any (·.isPrefixOf m)
  unless hits.isEmpty do
    throwError "[BROAD CONE] the closure of {target} reaches {hits}"
  let extra := cl.toList.filter fun m ↦
    Name.isPrefixOf `InfinitaryLogic m && !allowedProject.contains m
  unless extra.isEmpty do
    throwError "[BROAD CONE] the closure of {target} reaches project modules {extra}"

/-- The public declarations of the module (old and new). -/
def moduleDecls : List Name :=
  [`not_countable_univ_cantor, `iSup_lt_omega1_of_forall_lt, `countable_iff_rank_bounded,
   `compl_countable_of_loss, `mk_le_aleph_one_of_domains, `mk_eq_aleph_one_of_domains,
   `rankTail, `rankTail_zero, `rankTail_antitone, `compl_rankTail, `rankTail_diff_succ,
   `rankTail_eq_iInter_of_isSuccPrelimit, `rankTail_iInter, `rankTail_compl_countable,
   `rankTail_loss_countable, `rankTail_persistent_eq_empty, `rankTail_eq_empty_of_omega_one_le,
   `mk_le_aleph_one_of_countable_fibres, `mk_eq_aleph_one_of_countable_fibres,
   `rankTail_cofinal_losses_iff, `leastLevel, `leastLevel_mem, `leastLevel_lt_omega1,
   `setOf_leastLevel_eq_subset, `countable_fibres_leastLevel, `rankTail_leastLevel].map
    (`InfinitaryLogic ++ ·)

/-- The guard's own declarations whose axioms are audited. -/
def guardDecls : List Name :=
  [`nat_tails, `nat_conditional, `nat_not_cofinal, `rv_fibre, `rv_fib, `W_not_countable,
   `W_cofinal, `W_mk, `W_mk_le, `W_mk_domains, `empty_case, `Qb_cover, `Qb_levels, `Qb_applied,
   `uncovered_fails].map (`RankTailGuard ++ ·)

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in moduleDecls ++ guardDecls do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "Rank-tail regression guard: OK (applied: the tail lemmas on N with the zero rank, \
    countable complements and losses, no persistent core, empty tails from omega_1 on, \
    #N <= aleph_1, and the losses not cofinal; the countable ordinals ranked by value, singleton \
    fibres, uncountable, cofinal losses, cardinality aleph_1 through the countable-fibre theorem \
    and through mk_eq_aleph_one_of_domains, with the extracted upper half on its own; the empty \
    type; an overlapping cover of Bool whose least level picks the least index, with countable \
    fibres, the tail identity and the composite bound; the covering hypothesis shown necessary \
    for the tail identity; import closure reaching only OrdinalUtil in the project; standard \
    axioms)"
