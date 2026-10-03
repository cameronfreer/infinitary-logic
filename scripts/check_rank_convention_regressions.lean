/-
Regression guard for the rank conventions of the Scott layer: the cross-structure ordinals
(the element-based `sr`, `scottRank`, `elementRank` of `Scott/Rank.lean` and
`Scott/Height/RankBounds.lean`, the all-tuples `scottHeight` of `Scott/Height/Defs.lean` and the
empty-tuple `stabilizationOrdinal` of `Scott/Sentence.lean`), all in `Ordinal.{0}`, against the
internal (orbit) finite-tuple `internalScottRank` (`Scott/OrbitRank.lean`, `Ordinal.{w}`).
The convention table lives in the module docstring of `Scott/Height/Defs.lean`.

These are the empty-carrier and pure-set counterexamples behind the docstring corrections
there and in `Scott/Rank.lean`; everything is proved from existing API, no library declaration
is added.

* **The empty carrier** (`Language.empty`, `PEmpty` in an arbitrary universe).  `scottRank` is
  an empty supremum, `0`.  `scottHeight` and `stabilizationOrdinal` are both exactly `1`: the
  one-point structure `PUnit` is `0`-equivalent to `PEmpty` but not `1`-equivalent (the back
  move has nothing to answer with), and a `1`-equivalent structure is empty, hence isomorphic.
  So `scottHeight ≤ scottRank` and `stabilizationOrdinal ≤ scottRank` both **fail**, and
  `internalScottRank ≤ lift scottRank` fails too (the empty tuple contributes
  `orbitRank + 1 ≥ 1` to `internalScottRank`).
* **The pure set `ℕ`.**  Every element has `elementRank` exactly `ω` (at a finite level `k` the
  singleton `![m]` is `k`- but not `(k + 1)`-equivalent to `![0]` in `Fin (k + 1)`, while it is
  equivalent at every level to itself; at `ω` the partner structure is infinite, so an
  isomorphism carries `m` to the partner point), hence `scottRank ℕ = ω + 1`; and
  `stabilizationOrdinal ℕ = ω`.  So on `ℕ` the cross-structure `scottRank` exceeds
  `stabilizationOrdinal` by one, while on the empty carrier it is one below.  Against the
  internal rank `internalScottRank ℕ = 1` (`internalScottRank_pureSet`):
  `lift stabilizationOrdinal ≤ internalScottRank + n` fails for every finite `n`, and
  `lift scottRank ≤ internalScottRank + ω` fails.
* **The `+ ω` offset.**  On `ℕ`, `lift (stabilizationOrdinal ℕ) =
  internalScottRank ℕ + ω` (`lift_stabilizationOrdinal_nat_eq`, as `1 + ω = ω`) while no finite
  offset suffices.  The `+ ω` bounds for `stabilizationOrdinal` and `scottHeight` over the
  internal rank (not for `scottRank`, which needs `+ ω + 1` here) are proved in
  `Scott/RankConventions.lean` and attained on `ℕ`; their guard is
  `check_rank_conventions_regressions.lean`.  This guard does not use them.
* **The documented relations, applied.**  `sr_le_scottRank`, `sr_le_scottHeight_of` and
  `scottRank_le_scottHeight_succ_of` are applied on `ℕ` (giving `ω ≤ scottHeight ℕ`), and
  `elementRank_le_completeStab` at the Scott height; the exact values are instantiated at an
  explicit `Type 1` empty carrier.

No new module is introduced, so there is no import closure to check.  The guard's declarations,
the six definitions `scottRank`, `scottHeight`, `sr`, `stabilizationOrdinal`,
`internalScottRank`, `elementRank`, and the cited relations (`sr_le_scottRank`,
`sr_le_scottHeight_of`, `scottRank_le_scottHeight_succ_of`, `elementRank_le_completeStab`,
`orbitRank_add_one_le_internalScottRank`, `internalScottRank_pureSet`, with
`countableRefinementHypothesis`) use only the standard axioms.

Run with: lake env lean scripts/check_rank_convention_regressions.lean
-/
import InfinitaryLogic.Scott.Height.RankBounds
import InfinitaryLogic.Scott.PureSetThreshold

open Lean FirstOrder FirstOrder.Language Ordinal

universe w

noncomputable section

namespace RankConventionGuard

-- The unique empty-language structures on the empty and the one-point carrier.
local instance : Language.empty.Structure PEmpty.{w + 1} := Language.emptyStructure
local instance : Language.empty.Structure PUnit.{w + 1} := Language.emptyStructure

section Empty

theorem scottRank_pempty : scottRank (L := Language.empty) PEmpty.{w + 1} = 0 := by
  simp [scottRank]

theorem bfEquiv_zero_pempty_punit :
    BFEquiv (L := Language.empty) (0 : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → PEmpty.{w + 1}) (Fin.elim0 : Fin 0 → PUnit.{w + 1}) := by
  rw [BFEquiv.zero]; exact (PureSet.sameAtomicType_iff _ _).2 fun i ↦ i.elim0

/-- An empty-language structure that is `1`-equivalent to the empty carrier is empty. -/
theorem isEmpty_of_bfEquiv_one_pempty {N : Type w} [Language.empty.Structure N]
    {b : Fin 0 → N}
    (h : BFEquiv (L := Language.empty) (1 : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → PEmpty.{w + 1}) b) : IsEmpty N := by
  rw [show (1 : Ordinal.{0}) = Order.succ 0 by simp, BFEquiv.succ] at h
  exact ⟨fun y ↦ (h.2.2 y).choose.elim⟩

/-- The empty-language isomorphism between the empty carrier and an empty structure. -/
def pemptyEquiv (N : Type w) [Language.empty.Structure N] [IsEmpty N] :
    PEmpty.{w + 1} ≃[Language.empty] N :=
  { toEquiv := Equiv.equivOfIsEmpty _ _ }

theorem scottHeight_pempty_ne_zero :
    scottHeight (L := Language.empty) PEmpty.{w + 1} ≠ 0 := by
  intro h
  have hstab := scottHeight_stabilizesCompletely (L := Language.empty) PEmpty.{w + 1}
  rw [h] at hstab
  have h1 := (hstab 0 PUnit.{w + 1} Fin.elim0 Fin.elim0).1 bfEquiv_zero_pempty_punit
  rw [BFEquiv.succ] at h1
  exact (h1.2.2 PUnit.unit).choose.elim

theorem not_scottHeight_le_scottRank_pempty :
    ¬ scottHeight (L := Language.empty) PEmpty.{w + 1} ≤
      scottRank (L := Language.empty) PEmpty.{w + 1} := by
  rw [scottRank_pempty, nonpos_iff_eq_zero]; exact scottHeight_pempty_ne_zero

/-- On the empty carrier every level-`1` equivalence upgrades to level `2`. -/
theorem bfEquiv_succ_one_of_bfEquiv_one_pempty {n : ℕ} (a : Fin n → PEmpty.{w + 1}) (N : Type w)
    [Language.empty.Structure N] (b : Fin n → N)
    (h : BFEquiv (L := Language.empty) (1 : Ordinal.{0}) n a b) :
    BFEquiv (L := Language.empty) (Order.succ (1 : Ordinal.{0})) n a b := by
  cases n with
  | succ n => exact (a 0).elim
  | zero =>
    have hb : b = Fin.elim0 := funext fun i ↦ i.elim0
    have ha : a = Fin.elim0 := funext fun i ↦ i.elim0
    subst hb ha
    have := isEmpty_of_bfEquiv_one_pempty h
    simpa [comp_fin_elim0] using equiv_implies_BFEquiv (pemptyEquiv N) _ 0 Fin.elim0

/-- **Exact value**: the Scott height of the empty carrier is `1`. -/
theorem scottHeight_pempty : scottHeight (L := Language.empty) PEmpty.{w + 1} = 1 := by
  refine le_antisymm (csInf_le' ?_) (Order.one_le_iff_ne_zero.2 scottHeight_pempty_ne_zero)
  intro n a N _ _ b h
  exact bfEquiv_succ_one_of_bfEquiv_one_pempty a N b h

theorem stabilizationOrdinal_pempty_ne_zero :
    stabilizationOrdinal (L := Language.empty) PEmpty.{w + 1} ≠ 0 := by
  intro h
  have hs := stabilizationOrdinal_stabilizes (L := Language.empty) PEmpty.{w + 1}
  rw [h] at hs
  obtain ⟨e⟩ := (hs PUnit.{w + 1}).1 bfEquiv_zero_pempty_punit
  exact (e.symm PUnit.unit).elim

/-- **Exact value**: the stabilization ordinal of the empty carrier is `1`. -/
theorem stabilizationOrdinal_pempty :
    stabilizationOrdinal (L := Language.empty) PEmpty.{w + 1} = 1 := by
  refine le_antisymm (csInf_le' ?_)
    (Order.one_le_iff_ne_zero.2 stabilizationOrdinal_pempty_ne_zero)
  intro N _ _
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ ?_⟩
  · have := isEmpty_of_bfEquiv_one_pempty h
    exact ⟨pemptyEquiv N⟩
  · simpa [BFEquiv0, comp_fin_elim0] using equiv_implies_BFEquiv e 1 0 Fin.elim0

theorem not_stabilizationOrdinal_le_scottRank_pempty :
    ¬ stabilizationOrdinal (L := Language.empty) PEmpty.{w + 1} ≤
      scottRank (L := Language.empty) PEmpty.{w + 1} := by
  rw [scottRank_pempty, nonpos_iff_eq_zero]; exact stabilizationOrdinal_pempty_ne_zero

theorem internalScottRank_pempty_pos :
    0 < internalScottRank (L := Language.empty) PEmpty.{w + 1} :=
  lt_of_lt_of_le (by simp) (orbitRank_add_one_le_internalScottRank (L := Language.empty)
    (Fin.elim0 : Fin 0 → PEmpty.{w + 1}))

theorem not_internalScottRank_le_lift_scottRank_pempty :
    ¬ internalScottRank (L := Language.empty) PEmpty.{w + 1} ≤
      Ordinal.lift.{w} (scottRank (L := Language.empty) PEmpty.{w + 1}) := by
  rw [scottRank_pempty, Ordinal.lift_zero, nonpos_iff_eq_zero]
  exact internalScottRank_pempty_pos.ne'

end Empty

section Pure

open PureSet

theorem omega0_le_stabilizationOrdinal_nat :
    ω ≤ stabilizationOrdinal (L := Language.empty) ℕ := by
  have hmem := stabilizationOrdinal_stabilizes (L := Language.empty) ℕ
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ := Ordinal.lt_omega0.1 hlt
  have hbf := (bfEquiv_nat_fin_iff k k).2 le_rfl
  rw [← hk] at hbf
  obtain ⟨e⟩ := (hmem (Fin k)).1 hbf
  exact (isEmpty_equiv_of_infinite_finite (X := ℕ) (Y := Fin k)).false e

theorem not_lift_stabilizationOrdinal_le_internalScottRank_add_nat (n : ℕ) :
    ¬ Ordinal.lift.{0} (stabilizationOrdinal (L := Language.empty) ℕ) ≤
      internalScottRank (L := Language.empty) ℕ + n := by
  rw [internalScottRank_pureSet, Ordinal.lift_id]
  intro h
  exact absurd (omega0_le_stabilizationOrdinal_nat.trans h)
    (not_le.2 (by exact_mod_cast Ordinal.natCast_lt_omega0 (1 + n)))

theorem spare_single (k : ℕ) (y : Fin (k + 1)) : spare (![y] : Fin 1 → Fin (k + 1)) = k := by
  unfold spare; rw [Set.ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]; simp

theorem omega0_le_elementRank_nat (m : ℕ) :
    ω ≤ elementRank (L := Language.empty) (M := ℕ) m := by
  have hne : {α : Ordinal.{0} | ∀ (N : Type) [Language.empty.Structure N] [Countable N]
      (b : Fin 1 → N), BFEquiv (L := Language.empty) (M := ℕ) (N := N) α 1 ![m] b →
        ∀ (N' : Type) [Language.empty.Structure N'] [Countable N'] (b' : Fin 1 → N'),
          BFEquiv (L := Language.empty) (M := ℕ) (N := N') α 1 ![m] b' →
            (BFEquiv (L := Language.empty) (M := ℕ) (N := N) (Order.succ α) 1 ![m] b ↔
             BFEquiv (L := Language.empty) (M := ℕ) (N := N') (Order.succ α) 1 ![m] b')}.Nonempty
      := by
    have hstab := scottHeight_stabilizesCompletely (L := Language.empty) ℕ
    exact ⟨_, fun N _ _ b hb N' _ _ b' hb' ↦
      ⟨fun _ ↦ (hstab 1 N' ![m] b').1 hb', fun _ ↦ (hstab 1 N ![m] b).1 hb⟩⟩
  have hmem := csInf_mem hne
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ := Ordinal.lt_omega0.1 hlt
  unfold elementRank at hk
  rw [hk] at hmem
  have hpat : ∀ i j : Fin 1, (![m] : Fin 1 → ℕ) i = ![m] j ↔
      (![0] : Fin 1 → Fin (k + 1)) i = ![0] j := fun i j ↦ by
    simp [Subsingleton.elim i j]
  have hb : BFEquiv (L := Language.empty) (M := ℕ) (N := Fin (k + 1)) (k : Ordinal.{0}) 1
      ![m] ![0] := (bfEquiv_natCast_iff k _ _).2 ⟨hpat, (spare_single k 0).ge⟩
  have hsucc := (hmem (Fin (k + 1)) ![0] hb ℕ ![m] (BFEquiv.refl _ _)).2 (BFEquiv.refl _ _)
  rw [Order.succ_eq_add_one, show ((k : Ordinal.{0}) + 1) = ((k + 1 : ℕ) : Ordinal.{0}) by
    push_cast; rfl] at hsucc
  have := ((bfEquiv_natCast_iff (k + 1) _ _).1 hsucc).2
  rw [spare_single] at this
  omega

theorem omega0_add_one_le_scottRank_nat :
    ω + 1 ≤ scottRank (L := Language.empty) ℕ := by
  unfold scottRank
  have : Small.{0} ℕ := Countable.toSmall ℕ
  calc ω + 1 ≤ elementRank (L := Language.empty) (M := ℕ) 0 + 1 :=
        add_le_add_left (omega0_le_elementRank_nat 0) 1
    _ ≤ ⨆ m : ℕ, elementRank (L := Language.empty) (M := ℕ) m + 1 :=
        Ordinal.le_iSup (fun m : ℕ ↦ elementRank (L := Language.empty) (M := ℕ) m + 1) 0

theorem not_lift_scottRank_le_internalScottRank_add_omega0_nat :
    ¬ Ordinal.lift.{0} (scottRank (L := Language.empty) ℕ) ≤
      internalScottRank (L := Language.empty) ℕ + ω := by
  rw [internalScottRank_pureSet, Ordinal.lift_id, Ordinal.one_add_omega0]
  intro h
  exact absurd (omega0_add_one_le_scottRank_nat.trans h) (not_le.2 (Order.lt_add_one_iff.2 le_rfl))

/-- A countable empty-language structure that is `ω`-equivalent to `ℕ` (at any tuples) is
infinite. -/
theorem infinite_of_bfEquiv_omega0 {N : Type} [Language.empty.Structure N] {n : ℕ}
    {a : Fin n → ℕ} {b : Fin n → N}
    (h : BFEquiv (L := Language.empty) (ω : Ordinal.{0}) n a b) :
    Infinite N := by
  by_contra hfin
  have : Finite N := not_infinite_iff_finite.1 hfin
  have hk : BFEquiv (L := Language.empty) ((spare b + 1 : ℕ) : Ordinal.{0}) n a b :=
    BFEquiv.monotone (Ordinal.natCast_lt_omega0 (spare b + 1)).le h
  have := ((bfEquiv_natCast_iff (spare b + 1) a b).1 hk).2
  omega

/-- An isomorphism of `ℕ` onto a countably infinite empty-language structure carrying `m` to
a prescribed point. -/
theorem exists_natEquiv (N : Type) [Language.empty.Structure N] [Countable N] [Infinite N]
    (m : ℕ) (y : N) : ∃ e : ℕ ≃[Language.empty] N, e m = y := by
  classical
  obtain ⟨d⟩ := nonempty_denumerable N
  let e0 : ℕ ≃ N := (Denumerable.eqv N).symm
  refine ⟨{ toEquiv := e0.trans (Equiv.swap (e0 m) y) }, ?_⟩
  exact Equiv.swap_apply_left _ _

/-- **Exact value**: the stabilization ordinal of `ℕ` is `ω`. -/
theorem stabilizationOrdinal_nat : stabilizationOrdinal (L := Language.empty) ℕ = ω := by
  refine le_antisymm (csInf_le' ?_) omega0_le_stabilizationOrdinal_nat
  intro N _ _
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ ?_⟩
  · have := infinite_of_bfEquiv_omega0 h
    obtain ⟨e, -⟩ := exists_natEquiv N 0 (Classical.arbitrary N)
    exact ⟨e⟩
  · simpa [BFEquiv0, comp_fin_elim0] using equiv_implies_BFEquiv e ω 0 Fin.elim0

/-- **Exact value**: every element of `ℕ` has element rank `ω`. -/
theorem elementRank_nat (m : ℕ) : elementRank (L := Language.empty) (M := ℕ) m = ω := by
  refine le_antisymm (csInf_le' ?_) (omega0_le_elementRank_nat m)
  have hall : ∀ (N : Type) [Language.empty.Structure N] [Countable N] (b : Fin 1 → N),
      BFEquiv (L := Language.empty) (M := ℕ) (N := N) ω 1 ![m] b →
        BFEquiv (L := Language.empty) (M := ℕ) (N := N) (Order.succ ω) 1 ![m] b := by
    intro N _ _ b hb
    have := infinite_of_bfEquiv_omega0 hb
    obtain ⟨e, he⟩ := exists_natEquiv N m (b 0)
    have hb' : (⇑e ∘ ![m]) = b := funext fun i ↦ by
      rw [Subsingleton.elim i 0]; simpa using he
    simpa [hb'] using equiv_implies_BFEquiv e (Order.succ ω) 1 ![m]
  exact fun N _ _ b hb N' _ _ b' hb' ↦ ⟨fun _ ↦ hall N' b' hb', fun _ ↦ hall N b hb⟩

/-- **Exact value**: the Scott rank of `ℕ` is `ω + 1`. -/
theorem scottRank_nat : scottRank (L := Language.empty) ℕ = ω + 1 := by
  refine le_antisymm ?_ omega0_add_one_le_scottRank_nat
  unfold scottRank
  have : Small.{0} ℕ := Countable.toSmall ℕ
  exact Ordinal.iSup_le fun m ↦ by rw [elementRank_nat]

/-- On `ℕ` the stabilization ordinal equals the internal rank plus `ω` (`1 + ω = ω`). -/
theorem lift_stabilizationOrdinal_nat_eq :
    Ordinal.lift.{0} (stabilizationOrdinal (L := Language.empty) ℕ) =
      internalScottRank (L := Language.empty) ℕ + ω := by
  rw [internalScottRank_pureSet, Ordinal.lift_id, Ordinal.one_add_omega0, stabilizationOrdinal_nat]

end Pure

/-! ### The documented relations, applied -/

section Relations

/-- On the empty carrier the element-based `scottRank` is one **below** the stabilization
ordinal; on `ℕ` it is one **above**. -/
theorem scottRank_add_one_eq_stabilizationOrdinal_pempty_and_nat :
    scottRank (L := Language.empty) PEmpty.{w + 1} + 1 =
        stabilizationOrdinal (L := Language.empty) PEmpty.{w + 1} ∧
      scottRank (L := Language.empty) ℕ =
        stabilizationOrdinal (L := Language.empty) ℕ + 1 := by
  refine ⟨?_, ?_⟩
  · rw [scottRank_pempty, stabilizationOrdinal_pempty, zero_add]
  · rw [scottRank_nat, stabilizationOrdinal_nat]

/-- The proved relations named in the docs, applied on `ℕ`. -/
theorem documented_relations_nat :
    ω ≤ sr (L := Language.empty) ℕ ∧
      sr (L := Language.empty) ℕ ≤ scottRank (L := Language.empty) ℕ ∧
      sr (L := Language.empty) ℕ ≤ scottHeight (L := Language.empty) ℕ ∧
      ω ≤ scottHeight (L := Language.empty) ℕ ∧
      (∀ m : ℕ, elementRank (L := Language.empty) (M := ℕ) m ≤
        scottHeight (L := Language.empty) ℕ) := by
  have : Small.{0} ℕ := Countable.toSmall ℕ
  refine ⟨?_, sr_le_scottRank ℕ, sr_le_scottHeight_of countableRefinementHypothesis ℕ, ?_,
    fun m ↦ elementRank_le_completeStab (scottHeight_stabilizesCompletely ℕ) m⟩
  · rw [← elementRank_nat 0]
    exact Ordinal.le_iSup (fun m : ℕ ↦ elementRank (L := Language.empty) (M := ℕ) m) 0
  · have h := scottRank_le_scottHeight_succ_of (L := Language.empty)
      countableRefinementHypothesis ℕ
    rw [scottRank_nat] at h
    exact Order.le_of_succ_le_succ h

/-- The empty-carrier values at an explicit `Type 1` carrier. -/
theorem pempty_type_one_values :
    scottRank (L := Language.empty) PEmpty.{2} = 0 ∧
      scottHeight (L := Language.empty) PEmpty.{2} = 1 ∧
      stabilizationOrdinal (L := Language.empty) PEmpty.{2} = 1 ∧
      0 < internalScottRank (L := Language.empty) PEmpty.{2} :=
  ⟨scottRank_pempty, scottHeight_pempty, stabilizationOrdinal_pempty,
    internalScottRank_pempty_pos⟩

end Relations

/-! ### Axiom audit -/

/-- The library definitions whose conventions are documented. -/
def libraryDecls : List Name :=
  [`scottRank, `scottHeight, `sr, `stabilizationOrdinal, `internalScottRank, `elementRank,
   `sr_le_scottRank, `sr_le_scottHeight_of, `scottRank_le_scottHeight_succ_of,
   `elementRank_le_completeStab, `orbitRank_add_one_le_internalScottRank,
   `internalScottRank_pureSet, `countableRefinementHypothesis].map
    (`FirstOrder.Language ++ ·)

/-- The guard's own declarations whose axioms are audited. -/
def guardDecls : List Name :=
  [`scottRank_pempty, `bfEquiv_zero_pempty_punit, `isEmpty_of_bfEquiv_one_pempty,
   `pemptyEquiv, `scottHeight_pempty_ne_zero, `not_scottHeight_le_scottRank_pempty,
   `bfEquiv_succ_one_of_bfEquiv_one_pempty, `scottHeight_pempty,
   `stabilizationOrdinal_pempty_ne_zero,
   `stabilizationOrdinal_pempty, `not_stabilizationOrdinal_le_scottRank_pempty,
   `internalScottRank_pempty_pos, `not_internalScottRank_le_lift_scottRank_pempty,
   `omega0_le_stabilizationOrdinal_nat,
   `not_lift_stabilizationOrdinal_le_internalScottRank_add_nat, `spare_single,
   `omega0_le_elementRank_nat, `omega0_add_one_le_scottRank_nat,
   `not_lift_scottRank_le_internalScottRank_add_omega0_nat, `infinite_of_bfEquiv_omega0,
   `exists_natEquiv, `stabilizationOrdinal_nat, `elementRank_nat, `scottRank_nat,
   `lift_stabilizationOrdinal_nat_eq,
   `scottRank_add_one_eq_stabilizationOrdinal_pempty_and_nat, `documented_relations_nat,
   `pempty_type_one_values].map
    (`RankConventionGuard ++ ·)

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in libraryDecls ++ guardDecls do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "Rank-convention regression guard: OK (empty carrier: scottRank = 0, scottHeight = 1, \
    stabilizationOrdinal = 1, internalScottRank > 0, refuting scottHeight <= scottRank, \
    stabilizationOrdinal <= scottRank and internalScottRank <= lift scottRank, also at Type 1; \
    pure set N: elementRank = omega, scottRank = omega + 1, stabilizationOrdinal = omega, \
    refuting lift stabilizationOrdinal <= internalScottRank + n for finite n and \
    lift scottRank <= internalScottRank + omega, with lift stabilizationOrdinal = \
    internalScottRank + omega; the documented relations applied on N; \
    standard axioms)"

end RankConventionGuard
