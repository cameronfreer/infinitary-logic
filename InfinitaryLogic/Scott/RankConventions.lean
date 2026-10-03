/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.MontalbanQuantifierRank
import InfinitaryLogic.Scott.SentenceRecognition
import InfinitaryLogic.Scott.OrbitRankStabilization
import InfinitaryLogic.Scott.Height.RankBounds
import InfinitaryLogic.Scott.BFEquivRelabel

/-!
# Comparisons between the cross-structure and the internal Scott ranks

The library has two families of Scott-rank ordinals; the convention table is in the module
docstring of `Scott/Height/Defs.lean`.  The **cross-structure** ones (`stabilizationOrdinal`,
`scottHeight`, `sr`, `scottRank`) live in `Ordinal.{0}`; the **internal (orbit)** ones
(`orbitRank`, `internalScottRank`) live in `Ordinal.{w}` for `M : Type w`.  This module proves
the comparisons between the two families, always with `Ordinal.lift.{w}` on the `Ordinal.{0}`
side.  Write `R = ⨆ a, orbitRank a` for the supremum of the orbit ranks over all tuples
`Σ n, Fin n → M`.

**Headline.**  For a countable structure `M : Type w` over a relational language with countably
many relation symbols,

  `lift (stabilizationOrdinal M) ≤ internalScottRank M + ω`  and
  `lift (scottHeight M) ≤ internalScottRank M + ω`

(`lift_stabilizationOrdinal_le_internalScottRank_add_omega0`,
`lift_scottHeight_le_internalScottRank_add_omega0`).  The forms with `R + ω` on the right
(`lift_stabilizationOrdinal_le_iSup_orbitRank_add_omega0`,
`lift_scottHeight_le_iSup_orbitRank_add_omega0`) are the same statements: the two right-hand
sides are **equal**, `internalScottRank M + ω = R + ω` (`internalScottRank_add_omega0_eq`),
because `R ≤ internalScottRank M ≤ R + 1` and `1 + ω = ω`.  No `Nonempty` or `Infinite`
hypothesis is needed.

**The `+ ω` is needed, and the bounds are attained.**  On the infinite pure set `ℕ`,
`internalScottRank ℕ = 1` (`internalScottRank_pureSet`) while
`stabilizationOrdinal ℕ = scottHeight ℕ = ω`: both bounds are equalities there, and no finite
offset `internalScottRank M + n` suffices (`scripts/check_rank_conventions_regressions.lean`).

**Route.**
* *Descent.*  Every orbit rank is at most the lifted Scott height
  (`orbitRank_le_lift_scottHeight`), so `R = lift β` for some `β ≤ scottHeight M`
  (`exists_lift_eq_iSup_orbitRank`); in particular `β < ω₁`.
* *Orbit formulas.*  The Scott formulas `scottFormula a β` at that uniform level define the
  automorphism orbits (`isOrbitFormulaFamily_scottFormula`; pointed:
  `isOrbitFormulaFamilyPointed_scottFormula`), and each has quantifier rank at most `β`
  (`scottFormula_qrank_le`).
* *Recognition.*  Montalbán's sentence of that family characterizes `M` among countable
  structures (`montalbanSentence_characterizes`) and has quantifier rank at most `β + ω`
  (`qrank_montalbanSentence_le`), so `stabilizationOrdinal M ≤ β + ω` by
  `stabilizationOrdinal_le_of_formula_rank` (`Scott/SentenceRecognition.lean`).
* *Scott height.*  The identity
  `lift (scottHeight M) = max (lift (stabilizationOrdinal M)) R` (`lift_scottHeight_eq_max`)
  turns the stabilization bound into the Scott-height bound, as `R ≤ R + ω`.  Its `≤` half
  (`scottHeight_le_max_of_orbitRank_le`) restricts a pair of tuples to the empty tuple,
  recognizes the structures as isomorphic there, and moves the remaining pair of tuples of `M`
  by an automorphism (pointed Karp at the orbit rank).  The pointed sentence is not used; a
  second derivation through it is exercised in the regression guard only.

## Main declarations

* Any language, any structure: `internalScottRank_add_omega0_eq` (with
  `iSup_orbitRank_le_internalScottRank` and `internalScottRank_le_iSup_orbitRank_add_one` from
  `Scott/OrbitRankStabilization.lean`).
* Through `scottHeight`: `orbitRank_le_lift_scottHeight`, `exists_lift_eq_iSup_orbitRank`,
  `internalScottRank_le_lift_scottHeight_add_one`, `stabilizationOrdinal_le_scottHeight`,
  `scottHeight_le_max_of_orbitRank_le`, `lift_scottHeight_eq_max`.
* Orbit formulas: `isOrbitFormulaFamily_scottFormula`, `isOrbitFormulaFamilyPointed_scottFormula`.
* Unconditional element-based wrappers: `sr_le_scottHeight`, `scottRank_le_scottHeight_add_one`.
* The `+ ω` bounds: `lift_stabilizationOrdinal_le_internalScottRank_add_omega0`,
  `lift_scottHeight_le_internalScottRank_add_omega0`, and their `R` forms
  `lift_stabilizationOrdinal_le_iSup_orbitRank_add_omega0`,
  `lift_scottHeight_le_iSup_orbitRank_add_omega0`.

## Interpretation choices

* **Hypotheses.**  `[L.IsRelational]` and `[Countable (Σ l, L.Relations l)]`, as `scottHeight`
  and `montalbanSentence_characterizes` need; `M` countable.  The Scott height enters through
  `scottHeight_stabilizesCompletely` and `scottHeight_lt_omega1`, hence through
  `countableRefinementHypothesis`, which is proved with the standard axioms only.  The
  internal comparison `internalScottRank_add_omega0_eq` needs neither relationality nor
  countability.
* **Universes.**  `stabilizationOrdinal`, `scottHeight` and `qrank` are in `Ordinal.{0}`;
  `orbitRank` and `internalScottRank` in `Ordinal.{w}`.  The lift is on the `Ordinal.{0}` side;
  at `w = 0` it disappears by `Ordinal.lift_id`.
* **Quantifier rank, not signed classes.**  The recognition step uses the quantifier rank of
  `Scott/MontalbanQuantifierRank.lean`, not the signed `Σ^in`/`Π^in` classification of
  `Scott/MontalbanComplexity.lean`; no conversion between the two is used.

## What is not claimed

* Nothing is claimed about `scottHeight M ≤ scottRank M` for nonempty `M` (it fails on the
  empty carrier, `scripts/check_rank_convention_regressions.lean`).
* No converse bound `internalScottRank M ≤ lift (stabilizationOrdinal M) + c` is stated: it
  would need a type-omitting argument and is out of scope.
* For a structure whose internal rank is `ω` (such as the exact-`ω` carrier of
  `FiberExactOmega`), the bounds give only `≤ ω + ω`; nothing sharper is claimed there.
-/

universe u v w

namespace FirstOrder.Language

open BoundedFormulaω Ordinal

variable {L : Language.{u, v}}

/-! ### The internal rank under `+ ω` -/

/-- **Under `+ ω` the two internal conventions agree**: `internalScottRank M + ω = R + ω` with
`R = ⨆ a, orbitRank a`, since `R ≤ internalScottRank M ≤ R + 1` and `1 + ω = ω`.  Any
language, any structure. -/
theorem internalScottRank_add_omega0_eq (M : Type w) [L.Structure M] :
    internalScottRank (L := L) M + Ordinal.omega0 =
      (⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2) + Ordinal.omega0 := by
  refine le_antisymm ?_ (add_le_add_left iSup_orbitRank_le_internalScottRank _)
  calc internalScottRank (L := L) M + Ordinal.omega0
      ≤ (⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2) + 1 + Ordinal.omega0 :=
        add_le_add_left internalScottRank_le_iSup_orbitRank_add_one _
    _ = _ := by rw [add_assoc, Ordinal.one_add_omega0]

/-! ### Comparisons through `scottHeight` -/

section Comparisons

variable [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- **Descent**: every orbit rank of a countable `M` is at most its lifted Scott height. -/
theorem orbitRank_le_lift_scottHeight {M : Type w} [L.Structure M] [Countable M] {n : ℕ}
    (a : Fin n → M) : orbitRank (L := L) a ≤ Ordinal.lift.{w} (scottHeight (L := L) M) := by
  have hstab := scottHeight_stabilizesCompletely (L := L) M
  refine (selfStabilizesCompletely_iff_orbitRank_le.1 ?_) n a
  intro m x y
  refine ⟨fun h ↦ ?_, BFEquiv.of_succ⟩
  have h1 := BFEquiv.ofOrdinalLift ((hstab m M x y).1 (BFEquiv.toOrdinalLift h))
  rwa [Order.succ_eq_add_one, Ordinal.lift_add_one, ← Order.succ_eq_add_one] at h1

/-- The supremum of the orbit ranks of a countable `M` is the lift of an ordinal of
`Ordinal.{0}` at most `scottHeight M`. -/
theorem exists_lift_eq_iSup_orbitRank {M : Type w} [L.Structure M] [Countable M] :
    ∃ β : Ordinal.{0}, β ≤ scottHeight (L := L) M ∧
      Ordinal.lift.{w} β = ⨆ x : (Σ n, Fin n → M), orbitRank (L := L) x.2 := by
  have hle : (⨆ x : (Σ n, Fin n → M), orbitRank (L := L) x.2) ≤
      Ordinal.lift.{w} (scottHeight (L := L) M) :=
    iSup_orbitRank_le_iff.2 fun _ a ↦ orbitRank_le_lift_scottHeight a
  obtain ⟨β, hβ⟩ := Ordinal.mem_range_lift_of_le hle
  exact ⟨β, Ordinal.lift_le.1 (hβ ▸ hle), hβ⟩

/-- **Orbit formulas from Scott formulas**: if `β < ω₁` bounds every orbit rank (after the
lift), the Scott formulas `scottFormula a β` define the automorphism orbits of `M`. -/
theorem isOrbitFormulaFamily_scottFormula {M : Type w} [L.Structure M] [Countable M]
    {β : Ordinal.{0}} (hβ : β < Ordinal.omega 1)
    (hR : ∀ n (a : Fin n → M), orbitRank (L := L) a ≤ Ordinal.lift.{w} β) :
    IsOrbitFormulaFamily (L := L) (fun n (a : Fin n → M) ↦ scottFormula (L := L) a β) := by
  intro n a b
  rw [realize_scottFormula_iff_BFEquiv a b β hβ]
  exact ⟨fun h ↦ bfEquiv_orbitRank_iff_exists_automorphism.1
      (BFEquiv.monotone (hR n a) (BFEquiv.ofOrdinalLift h)),
    fun ⟨e, he⟩ ↦ BFEquiv.toOrdinalLift (bfEquiv_all_of_automorphism e he _)⟩

/-- **The pointed form**: under the same hypotheses, the Scott formulas of `c ⌢ a` at level `β`
define the orbits of the automorphisms fixing `c`. -/
theorem isOrbitFormulaFamilyPointed_scottFormula {M : Type w} [L.Structure M] [Countable M]
    {β : Ordinal.{0}} (hβ : β < Ordinal.omega 1)
    (hR : ∀ n (a : Fin n → M), orbitRank (L := L) a ≤ Ordinal.lift.{w} β) {k : ℕ}
    (c : Fin k → M) :
    IsOrbitFormulaFamilyPointed (L := L) c
      (fun n (a : Fin n → M) ↦ scottFormula (L := L) (Fin.append c a) β) := by
  intro n a b
  rw [realize_scottFormula_iff_BFEquiv _ _ β hβ]
  constructor
  · intro h
    obtain ⟨e, he⟩ := bfEquiv_orbitRank_iff_exists_automorphism.1
      (BFEquiv.monotone (hR _ _) (BFEquiv.ofOrdinalLift h))
    refine ⟨e, funext fun j ↦ ?_, funext fun j ↦ ?_⟩
    · simpa using congrFun he (Fin.castAdd n j)
    · simpa using congrFun he (Fin.natAdd k j)
  · rintro ⟨e, hc, ha⟩
    refine BFEquiv.toOrdinalLift (bfEquiv_all_of_automorphism e ?_ _)
    funext j
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
    · simpa using congrFun hc j
    · simpa using congrFun ha j

/-- Whole-model recognition happens no later than complete stabilization:
`stabilizationOrdinal M ≤ scottHeight M`. -/
theorem stabilizationOrdinal_le_scottHeight (M : Type w) [L.Structure M] [Countable M] :
    stabilizationOrdinal (L := L) M ≤ scottHeight (L := L) M := by
  refine csInf_le' fun N _ _ ↦ ⟨BFEquiv_stabilization_implies_equiv
    (scottHeight_stabilizesCompletely M), fun ⟨e⟩ ↦ ?_⟩
  simpa only [comp_fin_elim0] using equiv_implies_BFEquiv e (scottHeight (L := L) M) 0 Fin.elim0

/-- **Unpointed height bound**: if `β` bounds every orbit rank (after the lift), then
`scottHeight M ≤ max (stabilizationOrdinal M) β`.  A pair of tuples equivalent at that level is
equivalent at the empty tuple, so the structures are isomorphic; inside `M` the remaining pair
is then moved by an automorphism. -/
theorem scottHeight_le_max_of_orbitRank_le {M : Type w} [L.Structure M] [Countable M]
    {β : Ordinal.{0}} (hR : ∀ n (a : Fin n → M), orbitRank (L := L) a ≤ Ordinal.lift.{w} β) :
    scottHeight (L := L) M ≤ max (stabilizationOrdinal (L := L) M) β := by
  refine csInf_le' ?_
  intro n a N _ _ b hab
  have h0 := hab.relabel _ (Fin.elim0 : Fin 0 → Fin n)
  rw [show a ∘ Fin.elim0 = Fin.elim0 from funext (·.elim0),
    show b ∘ Fin.elim0 = Fin.elim0 from funext (·.elim0)] at h0
  obtain ⟨e⟩ := (stabilizationOrdinal_stabilizes (L := L) M N).1
    (BFEquiv.monotone (le_max_left _ _) h0)
  have hb' : BFEquiv (L := L) (max (stabilizationOrdinal (L := L) M) β) n a (e.symm ∘ b) :=
    hab.trans (equiv_implies_BFEquiv e.symm _ n b)
  obtain ⟨σ, hσ⟩ := bfEquiv_orbitRank_iff_exists_automorphism.1
    (BFEquiv.monotone ((hR n a).trans (Ordinal.lift_le.2 (le_max_right _ _)))
      (BFEquiv.ofOrdinalLift hb'))
  have hab' : ⇑(e.comp σ) ∘ a = b := by
    funext j
    have := congrFun hσ j
    simp only [Function.comp_apply] at this ⊢
    simp [Language.Equiv.comp_apply, this]
  rw [← hab']
  exact equiv_implies_BFEquiv _ _ n a

/-- **The Scott height is the maximum of whole-model recognition and the orbit ranks**:
`lift (scottHeight M) = max (lift (stabilizationOrdinal M)) (⨆ a, orbitRank a)`. -/
theorem lift_scottHeight_eq_max (M : Type w) [L.Structure M] [Countable M] :
    Ordinal.lift.{w} (scottHeight (L := L) M) =
      max (Ordinal.lift.{w} (stabilizationOrdinal (L := L) M))
        (⨆ x : (Σ n, Fin n → M), orbitRank (L := L) x.2) := by
  have hle : (⨆ x : (Σ n, Fin n → M), orbitRank (L := L) x.2) ≤
      Ordinal.lift.{w} (scottHeight (L := L) M) :=
    iSup_orbitRank_le_iff.2 fun _ a ↦ orbitRank_le_lift_scottHeight a
  obtain ⟨β, hβ⟩ := Ordinal.mem_range_lift_of_le hle
  refine le_antisymm ?_ (max_le (Ordinal.lift_le.2 (stabilizationOrdinal_le_scottHeight M)) hle)
  have h := Ordinal.lift_le.{w}.2 (scottHeight_le_max_of_orbitRank_le (L := L) (M := M)
    fun _ a ↦ hβ ▸ orbitRank_le_iSup_orbitRank a)
  rw [← hβ]
  rcases le_total (stabilizationOrdinal (L := L) M) β with h' | h'
  · rw [max_eq_right h'] at h; rwa [max_eq_right (Ordinal.lift_le.2 h')]
  · rw [max_eq_left h'] at h; rwa [max_eq_left (Ordinal.lift_le.2 h')]

/-- The internal Scott rank is at most the lifted Scott height plus one. -/
theorem internalScottRank_le_lift_scottHeight_add_one (M : Type w) [L.Structure M]
    [Countable M] :
    internalScottRank (L := L) M ≤ Ordinal.lift.{w} (scottHeight (L := L) M) + 1 :=
  internalScottRank_le fun _ a ↦ add_le_add_left (orbitRank_le_lift_scottHeight a) 1

/-- `sr M ≤ scottHeight M`: the unconditional form of `sr_le_scottHeight_of`, through
`countableRefinementHypothesis`. -/
theorem sr_le_scottHeight (M : Type w) [L.Structure M] [Countable M] :
    sr (L := L) M ≤ scottHeight (L := L) M :=
  sr_le_scottHeight_of countableRefinementHypothesis M

/-- `scottRank M ≤ scottHeight M + 1`: the unconditional form of
`scottRank_le_scottHeight_succ_of`, through `countableRefinementHypothesis`. -/
theorem scottRank_le_scottHeight_add_one (M : Type w) [L.Structure M] [Countable M] :
    scottRank (L := L) M ≤ scottHeight (L := L) M + 1 :=
  scottRank_le_scottHeight_succ_of countableRefinementHypothesis M

/-! ### The `+ ω` bounds -/

/-- **Whole-model recognition, `R` form**:
`lift (stabilizationOrdinal M) ≤ (⨆ a, orbitRank a) + ω`.  The right-hand side equals
`internalScottRank M + ω` (`internalScottRank_add_omega0_eq`); the headline is
`lift_stabilizationOrdinal_le_internalScottRank_add_omega0`.

Montalbán's sentence of the Scott formulas at the uniform level `β` with
`lift β = ⨆ a, orbitRank a` characterizes `M` and has quantifier rank at most `β + ω`;
`stabilizationOrdinal_le_of_formula_rank` turns this into the bound. -/
theorem lift_stabilizationOrdinal_le_iSup_orbitRank_add_omega0 (M : Type w) [L.Structure M]
    [Countable M] :
    Ordinal.lift.{w} (stabilizationOrdinal (L := L) M) ≤
      (⨆ x : (Σ n, Fin n → M), orbitRank (L := L) x.2) + Ordinal.omega0 := by
  obtain ⟨β, hβsh, hβ⟩ := exists_lift_eq_iSup_orbitRank (L := L) (M := M)
  have hβω : β < Ordinal.omega 1 := hβsh.trans_lt (scottHeight_lt_omega1 M)
  have hR : ∀ n (a : Fin n → M), orbitRank (L := L) a ≤ Ordinal.lift.{w} β :=
    fun _ a ↦ hβ ▸ orbitRank_le_iSup_orbitRank a
  have hst : stabilizationOrdinal (L := L) M ≤ β + Ordinal.omega0 :=
    stabilizationOrdinal_le_of_formula_rank _
      (montalbanSentence_characterizes (isOrbitFormulaFamily_scottFormula hβω hR))
      (qrank_montalbanSentence_le fun _ a ↦ scottFormula_qrank_le a β hβω)
  calc Ordinal.lift.{w} (stabilizationOrdinal (L := L) M)
      ≤ Ordinal.lift.{w} (β + Ordinal.omega0) := Ordinal.lift_le.2 hst
    _ = _ := by rw [Ordinal.lift_add, Ordinal.lift_omega0, hβ]

/-- **Whole-model recognition within `ω` of the internal rank**:
`lift (stabilizationOrdinal M) ≤ internalScottRank M + ω`.  Attained on the infinite pure set
`ℕ`, where no finite offset suffices. -/
theorem lift_stabilizationOrdinal_le_internalScottRank_add_omega0 (M : Type w) [L.Structure M]
    [Countable M] :
    Ordinal.lift.{w} (stabilizationOrdinal (L := L) M) ≤
      internalScottRank (L := L) M + Ordinal.omega0 :=
  (internalScottRank_add_omega0_eq (L := L) M).symm ▸
    lift_stabilizationOrdinal_le_iSup_orbitRank_add_omega0 M

/-- **Scott height, `R` form**: `lift (scottHeight M) ≤ (⨆ a, orbitRank a) + ω`, from the
identity `lift_scottHeight_eq_max` and the stabilization bound.  The right-hand side equals
`internalScottRank M + ω`; the headline is `lift_scottHeight_le_internalScottRank_add_omega0`. -/
theorem lift_scottHeight_le_iSup_orbitRank_add_omega0 (M : Type w) [L.Structure M]
    [Countable M] :
    Ordinal.lift.{w} (scottHeight (L := L) M) ≤
      (⨆ x : (Σ n, Fin n → M), orbitRank (L := L) x.2) + Ordinal.omega0 := by
  rw [lift_scottHeight_eq_max]
  exact max_le (lift_stabilizationOrdinal_le_iSup_orbitRank_add_omega0 M) le_self_add

/-- **Scott height within `ω` of the internal rank**:
`lift (scottHeight M) ≤ internalScottRank M + ω`.  Attained on the infinite pure set `ℕ`,
where no finite offset suffices. -/
theorem lift_scottHeight_le_internalScottRank_add_omega0 (M : Type w) [L.Structure M]
    [Countable M] :
    Ordinal.lift.{w} (scottHeight (L := L) M) ≤
      internalScottRank (L := L) M + Ordinal.omega0 :=
  (internalScottRank_add_omega0_eq (L := L) M).symm ▸
    lift_scottHeight_le_iSup_orbitRank_add_omega0 M

end Comparisons

end FirstOrder.Language
