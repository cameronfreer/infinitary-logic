/-
Regression guard for `InfinitaryLogic/Scott/InternalRankBounds.lean`: the comparisons between the
cross-structure ranks (`stabilizationOrdinal`, `scottHeight`, `sr`, `scottRank`, in
`Ordinal.{0}`) and the internal (orbit) ranks (`orbitRank`, `internalScottRank`, in
`Ordinal.{w}`), and the derived bounds
`lift (stabilizationOrdinal M) ≤ internalScottRank M + ω` and
`lift (scottHeight M) ≤ internalScottRank M + ω`.  (The counterexample guard for the
conventions themselves is `check_rank_convention_regressions.lean`.)

* **Every new theorem applied**, on the infinite pure set `ℕ` over `Language.empty`, with the
  promoted `iSup_orbitRank_le_internalScottRank` and
  `internalScottRank_le_iSup_orbitRank_add_one` (`Scott/OrbitRankStabilization.lean`) and the
  three additions to `Scott/Height/RankBounds.lean` (`stabilizationOrdinal_le_scottHeight`,
  `sr_le_scottHeight`, `scottRank_le_scottHeight_succ`).
* **A second derivation of the Scott-height bound** through the pointed sentence, declared
  here and not in the library: the pointed recognition link
  `scottHeight_le_of_pointed_characterizes_of_qrank_le` (uniformly bounded pointed Scott
  specifications bound `scottHeight`) and
  `lift_scottHeight_le_iSup_orbitRank_add_omega0_pointed`.  The library derives the bound
  from the identity `lift_scottHeight_eq_max` instead.
* **Sharpness on `ℕ`** (internal rank `1`): `lift (stabilizationOrdinal ℕ) =
  internalScottRank ℕ + ω` and the same for `scottHeight`, the upper bounds coming from the new
  theorems and only the lower bound `ω ≤ stabilizationOrdinal ℕ` proved here (a copy of the
  #155 guard's theorem); no finite offset suffices for either, read off the two equalities;
  the exact values `internalScottRank ℕ = 1` and
  `stabilizationOrdinal ℕ = scottHeight ℕ = ω`; the orbit-rank supremum is `0` and the `R` form
  is an equality too.
* **A `Type 1` carrier**, `ULift.{1} ℕ`: all four bounds, the identity
  `lift_scottHeight_eq_max` and the pointed route, with `Ordinal.lift.{1}` on the left.
* **The empty carrier** `PEmpty` in an arbitrary universe: the two internal-rank bounds (no
  `Nonempty` hypothesis).
* **Import closure** of `Scott.InternalRankBounds`: exactly the 27 expected `InfinitaryLogic`
  modules (`[CLOSURE DRIFT]` otherwise).  The closure check and the axiom audit share one
  command, so the final OK line is printed only if both pass.
* **Standard axioms** for every public declaration of the module, the two promoted
  comparisons, and the guard's own theorems.

Run with: lake env lean scripts/check_internal_rank_bounds_regressions.lean
-/
import InfinitaryLogic.Scott.InternalRankBounds
import InfinitaryLogic.Scott.PureSetThreshold

set_option warningAsError true

open Lean FirstOrder FirstOrder.Language Ordinal

universe u v w

noncomputable section

namespace InternalRankBoundsGuard

/-! ### The second route: the pointed sentence -/

section Pointed

variable {L : Language.{u, v}} [L.IsRelational]

/-- **Pointed recognition link**: if every parameter tuple `c` of `M` has a pointed Scott
specification of quantifier rank at most `β`, then `scottHeight M ≤ β`. -/
theorem scottHeight_le_of_pointed_characterizes_of_qrank_le {M : Type w} [L.Structure M]
    [Countable M] {β : Ordinal.{0}}
    (h : ∀ (k : ℕ) (c : Fin k → M), ∃ φ : L.Formulaω (Fin k), φ.qrank ≤ β ∧
      ∀ (N : Type w) [L.Structure N] [Countable N] (d : Fin k → N),
        φ.Realize d ↔ ∃ e : M ≃[L] N, ⇑e ∘ c = d) :
    scottHeight (L := L) M ≤ β := by
  refine csInf_le' ?_
  intro n a N _ _ b hab
  obtain ⟨φ, hφ, hchar⟩ := h n a
  have ha : φ.Realize a := (hchar M a).2 ⟨Language.Equiv.refl L M, rfl⟩
  obtain ⟨e, rfl⟩ := (hchar N b).1 ((BFEquiv_implies_agreeQR β a b hab φ hφ).1 ha)
  exact equiv_implies_BFEquiv e _ n a

variable [Countable (Σ l, L.Relations l)]

/-- **Second derivation** of `lift_scottHeight_le_iSup_orbitRank_add_omega0`, through the
pointed sentences of the Scott formulas at the uniform level and the pointed link. -/
theorem lift_scottHeight_le_iSup_orbitRank_add_omega0_pointed (M : Type w) [L.Structure M]
    [Countable M] :
    Ordinal.lift.{w} (scottHeight (L := L) M) ≤
      (⨆ x : (Σ n, Fin n → M), orbitRank (L := L) x.2) + ω := by
  obtain ⟨β, hβsh, hβ⟩ := exists_lift_eq_iSup_orbitRank (L := L) (M := M)
  have hβω : β < Ordinal.omega 1 := hβsh.trans_lt (scottHeight_lt_omega1 M)
  have hR : ∀ n (a : Fin n → M), orbitRank (L := L) a ≤ Ordinal.lift.{w} β :=
    fun _ a ↦ hβ ▸ orbitRank_le_iSup_orbitRank a
  have hsh : scottHeight (L := L) M ≤ β + ω :=
    scottHeight_le_of_pointed_characterizes_of_qrank_le fun _ c ↦
      ⟨_, qrank_montalbanSentencePointed_le c fun _ _ ↦ scottFormula_qrank_le _ β hβω,
        fun N _ _ d ↦ montalbanSentencePointed_characterizes
          (isOrbitFormulaFamilyPointed_scottFormula hβω hR c) N d⟩
  calc Ordinal.lift.{w} (scottHeight (L := L) M)
      ≤ Ordinal.lift.{w} (β + ω) := Ordinal.lift_le.2 hsh
    _ = _ := by rw [Ordinal.lift_add, Ordinal.lift_omega0, hβ]

/-- The two routes give the same bound (a statement-level check). -/
theorem pointed_route_agrees (M : Type w) [L.Structure M] [Countable M] :
    (Ordinal.lift.{w} (scottHeight (L := L) M) ≤
        (⨆ x : (Σ n, Fin n → M), orbitRank (L := L) x.2) + ω) ∧
      (Ordinal.lift.{w} (scottHeight (L := L) M) ≤
        (⨆ x : (Σ n, Fin n → M), orbitRank (L := L) x.2) + ω) :=
  ⟨lift_scottHeight_le_iSup_orbitRank_add_omega0 M,
    lift_scottHeight_le_iSup_orbitRank_add_omega0_pointed M⟩

end Pointed

/-! ### Every new theorem, applied on `ℕ` -/

section Applied

open PureSet

/-- The orbit-rank supremum of `ℕ` is `0` (every orbit rank is `0`). -/
theorem iSup_orbitRank_nat :
    (⨆ x : (Σ n, Fin n → ℕ), orbitRank (L := Language.empty) x.2) = 0 :=
  le_antisymm (iSup_orbitRank_le_iff.2 fun _ a ↦ (orbitRank_pureSet a).le) zero_le

/-- The internal comparisons on `ℕ`, including the promoted ones. -/
theorem internal_applied_nat :
    (⨆ x : (Σ n, Fin n → ℕ), orbitRank (L := Language.empty) x.2) ≤
        internalScottRank (L := Language.empty) ℕ ∧
      internalScottRank (L := Language.empty) ℕ ≤
        (⨆ x : (Σ n, Fin n → ℕ), orbitRank (L := Language.empty) x.2) + 1 ∧
      internalScottRank (L := Language.empty) ℕ + ω =
        (⨆ x : (Σ n, Fin n → ℕ), orbitRank (L := Language.empty) x.2) + ω :=
  ⟨iSup_orbitRank_le_internalScottRank, internalScottRank_le_iSup_orbitRank_add_one,
    internalScottRank_add_omega0_eq ℕ⟩

/-- The comparisons through `scottHeight` on `ℕ`. -/
theorem height_applied_nat :
    orbitRank (L := Language.empty) (![0, 0] : Fin 2 → ℕ) ≤
        Ordinal.lift.{0} (scottHeight (L := Language.empty) ℕ) ∧
      (∃ β : Ordinal.{0}, β ≤ scottHeight (L := Language.empty) ℕ ∧
        Ordinal.lift.{0} β = ⨆ x : (Σ n, Fin n → ℕ), orbitRank (L := Language.empty) x.2) ∧
      stabilizationOrdinal (L := Language.empty) ℕ ≤ scottHeight (L := Language.empty) ℕ ∧
      scottHeight (L := Language.empty) ℕ ≤ max (stabilizationOrdinal (L := Language.empty) ℕ) 0 ∧
      Ordinal.lift.{0} (scottHeight (L := Language.empty) ℕ) =
        max (Ordinal.lift.{0} (stabilizationOrdinal (L := Language.empty) ℕ))
          (⨆ x : (Σ n, Fin n → ℕ), orbitRank (L := Language.empty) x.2) ∧
      internalScottRank (L := Language.empty) ℕ ≤
        Ordinal.lift.{0} (scottHeight (L := Language.empty) ℕ) + 1 ∧
      sr (L := Language.empty) ℕ ≤ scottHeight (L := Language.empty) ℕ ∧
      scottRank (L := Language.empty) ℕ ≤ scottHeight (L := Language.empty) ℕ + 1 :=
  ⟨orbitRank_le_lift_scottHeight _, exists_lift_eq_iSup_orbitRank,
    stabilizationOrdinal_le_scottHeight ℕ,
    scottHeight_le_max_of_orbitRank_le fun _ a ↦ by rw [orbitRank_pureSet, Ordinal.lift_zero],
    lift_scottHeight_eq_max ℕ, internalScottRank_le_lift_scottHeight_add_one ℕ,
    sr_le_scottHeight ℕ, scottRank_le_scottHeight_succ ℕ⟩

/-- The orbit-formula families of Scott formulas on `ℕ` at level `0`, unpointed and over the
repeated parameters `(3, 3)`. -/
theorem orbitFamilies_applied_nat :
    IsOrbitFormulaFamily (L := Language.empty)
        (fun n (a : Fin n → ℕ) ↦ scottFormula (L := Language.empty) a (0 : Ordinal.{0})) ∧
      IsOrbitFormulaFamilyPointed (L := Language.empty) (![3, 3] : Fin 2 → ℕ)
        (fun n (a : Fin n → ℕ) ↦
          scottFormula (L := Language.empty) (Fin.append (![3, 3] : Fin 2 → ℕ) a)
            (0 : Ordinal.{0})) := by
  have hω : (0 : Ordinal.{0}) < Ordinal.omega 1 := Ordinal.omega_pos 1
  have hR : ∀ n (a : Fin n → ℕ), orbitRank (L := Language.empty) a ≤ Ordinal.lift.{0} 0 :=
    fun _ a ↦ by rw [orbitRank_pureSet, Ordinal.lift_zero]
  exact ⟨isOrbitFormulaFamily_scottFormula hω hR,
    isOrbitFormulaFamilyPointed_scottFormula hω hR _⟩

/-- The four `+ ω` bounds on `ℕ`, and the pointed route. -/
theorem bounds_applied_nat :
    Ordinal.lift.{0} (stabilizationOrdinal (L := Language.empty) ℕ) ≤
        internalScottRank (L := Language.empty) ℕ + ω ∧
      Ordinal.lift.{0} (scottHeight (L := Language.empty) ℕ) ≤
        internalScottRank (L := Language.empty) ℕ + ω ∧
      Ordinal.lift.{0} (stabilizationOrdinal (L := Language.empty) ℕ) ≤
        (⨆ x : (Σ n, Fin n → ℕ), orbitRank (L := Language.empty) x.2) + ω ∧
      Ordinal.lift.{0} (scottHeight (L := Language.empty) ℕ) ≤
        (⨆ x : (Σ n, Fin n → ℕ), orbitRank (L := Language.empty) x.2) + ω ∧
      Ordinal.lift.{0} (scottHeight (L := Language.empty) ℕ) ≤
        (⨆ x : (Σ n, Fin n → ℕ), orbitRank (L := Language.empty) x.2) + ω :=
  ⟨lift_stabilizationOrdinal_le_internalScottRank_add_omega0 ℕ,
    lift_scottHeight_le_internalScottRank_add_omega0 ℕ,
    lift_stabilizationOrdinal_le_iSup_orbitRank_add_omega0 ℕ,
    lift_scottHeight_le_iSup_orbitRank_add_omega0 ℕ,
    lift_scottHeight_le_iSup_orbitRank_add_omega0_pointed ℕ⟩

end Applied

/-! ### Sharpness on the infinite pure set -/

section Sharpness

open PureSet

-- Copy of `RankConventionGuard.omega0_le_stabilizationOrdinal_nat` (the original is in
-- `check_rank_convention_regressions.lean`): a library home would add imports to
-- `Scott/PureSetThreshold.lean`, which does not reach `Scott/RefinementCount.lean`.
/-- The lower bound `ω ≤ stabilizationOrdinal ℕ`: a finite level `k` cannot tell `ℕ` from
`Fin k`. -/
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

/-- **The stabilization bound is attained on `ℕ`**: the upper bound is
`lift_stabilizationOrdinal_le_internalScottRank_add_omega0`. -/
theorem lift_stabilizationOrdinal_nat_eq :
    Ordinal.lift.{0} (stabilizationOrdinal (L := Language.empty) ℕ) =
      internalScottRank (L := Language.empty) ℕ + ω := by
  refine le_antisymm (lift_stabilizationOrdinal_le_internalScottRank_add_omega0 ℕ) ?_
  rw [internalScottRank_pureSet, Ordinal.lift_id, Ordinal.one_add_omega0]
  exact omega0_le_stabilizationOrdinal_nat

/-- **The Scott-height bound is attained on `ℕ`**: the upper bound is
`lift_scottHeight_le_internalScottRank_add_omega0`. -/
theorem lift_scottHeight_nat_eq :
    Ordinal.lift.{0} (scottHeight (L := Language.empty) ℕ) =
      internalScottRank (L := Language.empty) ℕ + ω := by
  refine le_antisymm (lift_scottHeight_le_internalScottRank_add_omega0 ℕ) ?_
  rw [internalScottRank_pureSet, Ordinal.lift_id, Ordinal.one_add_omega0]
  exact omega0_le_stabilizationOrdinal_nat.trans (stabilizationOrdinal_le_scottHeight ℕ)

/-- The exact values on `ℕ`: `internalScottRank ℕ = 1` and
`stabilizationOrdinal ℕ = scottHeight ℕ = ω`. -/
theorem nat_values :
    internalScottRank (L := Language.empty) ℕ = 1 ∧
      stabilizationOrdinal (L := Language.empty) ℕ = ω ∧
      scottHeight (L := Language.empty) ℕ = ω := by
  have h1 := lift_stabilizationOrdinal_nat_eq
  have h2 := lift_scottHeight_nat_eq
  rw [internalScottRank_pureSet, Ordinal.lift_id, Ordinal.one_add_omega0] at h1 h2
  exact ⟨internalScottRank_pureSet, h1, h2⟩

/-- **No finite offset suffices**, for the stabilization ordinal and for the Scott height:
read off the two equalities `lift_stabilizationOrdinal_nat_eq` and `lift_scottHeight_nat_eq`,
as `1 + ω = ω > 1 + n`. -/
theorem not_le_internalScottRank_add_nat (n : ℕ) :
    ¬ Ordinal.lift.{0} (stabilizationOrdinal (L := Language.empty) ℕ) ≤
        internalScottRank (L := Language.empty) ℕ + n ∧
      ¬ Ordinal.lift.{0} (scottHeight (L := Language.empty) ℕ) ≤
        internalScottRank (L := Language.empty) ℕ + n := by
  rw [lift_stabilizationOrdinal_nat_eq, lift_scottHeight_nat_eq, internalScottRank_pureSet,
    Ordinal.one_add_omega0, and_self]
  exact not_le.2 (by exact_mod_cast Ordinal.natCast_lt_omega0 (1 + n))

/-- The `R` form is an equality on `ℕ` as well: `R = 0` and `lift (stabilizationOrdinal ℕ) =
lift (scottHeight ℕ) = 0 + ω`. -/
theorem nat_iSup_orbitRank_add_omega0 :
    Ordinal.lift.{0} (stabilizationOrdinal (L := Language.empty) ℕ) =
        (⨆ x : (Σ n, Fin n → ℕ), orbitRank (L := Language.empty) x.2) + ω ∧
      Ordinal.lift.{0} (scottHeight (L := Language.empty) ℕ) =
        (⨆ x : (Σ n, Fin n → ℕ), orbitRank (L := Language.empty) x.2) + ω := by
  rw [← internalScottRank_add_omega0_eq]
  exact ⟨lift_stabilizationOrdinal_nat_eq, lift_scottHeight_nat_eq⟩

end Sharpness

/-! ### Universes and the empty carrier -/

section Universes

local instance : Language.empty.Structure (ULift.{1} ℕ) := Language.emptyStructure
local instance : Language.empty.Structure PEmpty.{w + 1} := Language.emptyStructure

/-- The `Type 1` carrier `ULift.{1} ℕ`: the four bounds, the identity and the pointed route,
with `Ordinal.lift.{1}` on the left. -/
theorem ulift_bounds :
    Ordinal.lift.{1} (stabilizationOrdinal (L := Language.empty) (ULift.{1} ℕ)) ≤
        internalScottRank (L := Language.empty) (ULift.{1} ℕ) + ω ∧
      Ordinal.lift.{1} (scottHeight (L := Language.empty) (ULift.{1} ℕ)) ≤
        internalScottRank (L := Language.empty) (ULift.{1} ℕ) + ω ∧
      Ordinal.lift.{1} (stabilizationOrdinal (L := Language.empty) (ULift.{1} ℕ)) ≤
        (⨆ x : (Σ n, Fin n → ULift.{1} ℕ), orbitRank (L := Language.empty) x.2) + ω ∧
      Ordinal.lift.{1} (scottHeight (L := Language.empty) (ULift.{1} ℕ)) ≤
        (⨆ x : (Σ n, Fin n → ULift.{1} ℕ), orbitRank (L := Language.empty) x.2) + ω ∧
      Ordinal.lift.{1} (scottHeight (L := Language.empty) (ULift.{1} ℕ)) =
        max (Ordinal.lift.{1} (stabilizationOrdinal (L := Language.empty) (ULift.{1} ℕ)))
          (⨆ x : (Σ n, Fin n → ULift.{1} ℕ), orbitRank (L := Language.empty) x.2) ∧
      Ordinal.lift.{1} (scottHeight (L := Language.empty) (ULift.{1} ℕ)) ≤
        (⨆ x : (Σ n, Fin n → ULift.{1} ℕ), orbitRank (L := Language.empty) x.2) + ω :=
  ⟨lift_stabilizationOrdinal_le_internalScottRank_add_omega0 _,
    lift_scottHeight_le_internalScottRank_add_omega0 _,
    lift_stabilizationOrdinal_le_iSup_orbitRank_add_omega0 _,
    lift_scottHeight_le_iSup_orbitRank_add_omega0 _,
    lift_scottHeight_eq_max _,
    lift_scottHeight_le_iSup_orbitRank_add_omega0_pointed _⟩

/-- The empty carrier, in any universe: the two internal-rank bounds. -/
theorem pempty_bounds :
    Ordinal.lift.{w} (stabilizationOrdinal (L := Language.empty) PEmpty.{w + 1}) ≤
        internalScottRank (L := Language.empty) PEmpty.{w + 1} + ω ∧
      Ordinal.lift.{w} (scottHeight (L := Language.empty) PEmpty.{w + 1}) ≤
        internalScottRank (L := Language.empty) PEmpty.{w + 1} + ω :=
  ⟨lift_stabilizationOrdinal_le_internalScottRank_add_omega0 _,
    lift_scottHeight_le_internalScottRank_add_omega0 _⟩

end Universes

end InternalRankBoundsGuard

end

/-! ### Import closure and axiom audit -/

/-- The modules transitively imported by `m` (including `m`), read from the environment
header. -/
partial def InternalRankBoundsGuard.importClosure (env : Environment) (m : Name) : NameSet :=
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

namespace InternalRankBoundsGuard

/-- The exact `InfinitaryLogic` part of the import closure of `Scott.InternalRankBounds`:
27 modules, the 19 of `Scott.MontalbanQuantifierRank` and eight more. -/
def expectedClosure : List Name :=
  [`InfinitaryLogic.Util, `InfinitaryLogic.OrdinalUtil, `InfinitaryLogic.Lomega1omega.Syntax,
   `InfinitaryLogic.Lomega1omega.Semantics, `InfinitaryLogic.Lomega1omega.Operations,
   `InfinitaryLogic.Lomega1omega.OpenBoundsSemantics, `InfinitaryLogic.Lomega1omega.QuantifierRank,
   `InfinitaryLogic.Lomega1omega.Theory, `InfinitaryLogic.Scott.AtomicDiagram,
   `InfinitaryLogic.Scott.BackAndForth, `InfinitaryLogic.Scott.BFEquivRelabel,
   `InfinitaryLogic.Scott.Formula, `InfinitaryLogic.Scott.Sentence,
   `InfinitaryLogic.Scott.Stabilization, `InfinitaryLogic.Scott.OrbitRank,
   `InfinitaryLogic.Scott.MontalbanSentence, `InfinitaryLogic.Scott.QuantifierRank,
   `InfinitaryLogic.Karp.PotentialIso, `InfinitaryLogic.Karp.CarrierTheorem,
   `InfinitaryLogic.Scott.MontalbanQuantifierRank, `InfinitaryLogic.Scott.SentenceRecognition,
   `InfinitaryLogic.Scott.OrbitRankStabilization, `InfinitaryLogic.Scott.Rank,
   `InfinitaryLogic.Scott.RefinementCount, `InfinitaryLogic.Scott.Height.Defs,
   `InfinitaryLogic.Scott.Height.RankBounds, `InfinitaryLogic.Scott.InternalRankBounds]

/-- The public declarations of `Scott.InternalRankBounds`, the two promoted comparisons of
`Scott.OrbitRankStabilization`, and the three additions to `Scott.Height.RankBounds`. -/
def libraryDecls : List Name :=
  [`iSup_orbitRank_le_internalScottRank, `internalScottRank_le_iSup_orbitRank_add_one,
   `internalScottRank_add_omega0_eq, `orbitRank_le_lift_scottHeight,
   `exists_lift_eq_iSup_orbitRank, `isOrbitFormulaFamily_scottFormula,
   `isOrbitFormulaFamilyPointed_scottFormula, `stabilizationOrdinal_le_scottHeight,
   `scottHeight_le_max_of_orbitRank_le, `lift_scottHeight_eq_max,
   `internalScottRank_le_lift_scottHeight_add_one, `sr_le_scottHeight,
   `scottRank_le_scottHeight_succ, `lift_stabilizationOrdinal_le_iSup_orbitRank_add_omega0,
   `lift_stabilizationOrdinal_le_internalScottRank_add_omega0,
   `lift_scottHeight_le_iSup_orbitRank_add_omega0,
   `lift_scottHeight_le_internalScottRank_add_omega0].map (`FirstOrder.Language ++ ·)

/-- The guard's own theorems whose axioms are audited. -/
def guardDecls : List Name :=
  [`scottHeight_le_of_pointed_characterizes_of_qrank_le,
   `lift_scottHeight_le_iSup_orbitRank_add_omega0_pointed, `pointed_route_agrees,
   `iSup_orbitRank_nat, `internal_applied_nat, `height_applied_nat,
   `orbitFamilies_applied_nat, `bounds_applied_nat, `omega0_le_stabilizationOrdinal_nat,
   `lift_stabilizationOrdinal_nat_eq, `lift_scottHeight_nat_eq, `nat_values,
   `not_le_internalScottRank_add_nat, `nat_iSup_orbitRank_add_omega0,
   `ulift_bounds, `pempty_bounds].map (`InternalRankBoundsGuard ++ ·)

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

end InternalRankBoundsGuard

open InternalRankBoundsGuard in
-- The closure check and the axiom audit run in one command, so that the final OK line is
-- printed only when both pass.
run_cmd do
  let env ← getEnv
  let target := `InfinitaryLogic.Scott.InternalRankBounds
  unless (env.getModuleIdx? target).isSome do
    throwError "module {target} is not in the environment"
  let cl := importClosure env target
  let il := cl.toList.filter (`InfinitaryLogic).isPrefixOf
  let extra := il.filter fun m ↦ !expectedClosure.contains m
  let missing := expectedClosure.filter fun m ↦ !cl.contains m
  unless extra.isEmpty && missing.isEmpty do
    throwError "[CLOSURE DRIFT] the closure of {target}: unexpected {extra}, missing {missing}"
  unless il.length == expectedClosure.length do
    throwError "[CLOSURE DRIFT] the closure of {target} has {il.length} modules, not \
      {expectedClosure.length}"
  for n in libraryDecls ++ guardDecls do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "Internal-rank-bounds regression guard: OK (every new comparison applied on N, with the \
    promoted internal comparisons; the Scott-height bound derived a second time through the \
    pointed sentence and the guard-local pointed link; on N: lift stabilizationOrdinal = \
    lift scottHeight = internalScottRank + omega, internalScottRank = 1, \
    stabilizationOrdinal = scottHeight = omega, the orbit-rank supremum 0, and no finite offset \
    suffices for either; at ULift.{1} N the four bounds, the max identity and the pointed route; \
    on PEmpty in any universe the two internal-rank bounds; exact import closure of 27 \
    modules; standard axioms)"
