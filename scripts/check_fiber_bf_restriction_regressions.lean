/-
Regression guard for the pointed back-and-forth restriction
(`ModelTheory/FiberBFRestriction.lean`).

Two instances over two rows (`Bool`).  Positive, successor level: constant `Bool` fibers with the
row swap; the pointed tuple `(row true, pt true)` is assembled to level `1` (item 3) and the
restriction returns level-`1` equivalence of the component points.  Negative, level zero with an
**empty fiber and a nullary fact**: fibers `Unit` (nullary symbol false) and `Empty` (nullary
symbol true); the contrapositive of the empty-tuple corollary shows the two rows are not
`BFEquiv 0` in the assembled language, so lifted nullary facts distinguish rows at level zero.
Headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_fiber_bf_restriction_regressions.lean
-/
import InfinitaryLogic.ModelTheory.FiberBFRestriction
import InfinitaryLogic.ModelTheory.FiberBFAssembly
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

open Lean FirstOrder Language FiberAssembly

/-- The component language: one binary symbol `e`, one nullary symbol `c`. -/
inductive CSym : ℕ → Type
  | e : CSym 2
  | c : CSym 0

/-- The component language. -/
abbrev Lc : Language := ⟨fun _ => Empty, CSym⟩

/-- The component `Bool`: `e` is inequality, `c` fails. -/
instance instBoolC : Lc.Structure Bool where
  funMap f _ := (f : Empty).elim
  RelMap {n} R v := match n, R with
    | _, CSym.e => v 0 ≠ v 1
    | _, CSym.c => False

/-- The component `Unit`: the nullary symbol fails. -/
instance instUnitC : Lc.Structure Unit where
  funMap f _ := (f : Empty).elim
  RelMap {n} R _ := match n, R with
    | _, CSym.e => False
    | _, CSym.c => False

/-- The empty component: the nullary symbol holds. -/
instance instEmptyC : Lc.Structure Empty where
  funMap f _ := (f : Empty).elim
  RelMap {n} R _ := match n, R with
    | _, CSym.e => False
    | _, CSym.c => True

/-- A label. -/
def lab0 : Label ℕ := ⟨[0], by decide⟩

/-! ### Positive, successor level -/

abbrev Cb : Bool → Label ℕ → Type := fun _ _ => Bool

/-- The row swap. -/
def swap : Bool ≃ Bool := ⟨not, not, Bool.not_not, Bool.not_not⟩

/-- The pointed tuples `(row true, pt true)` and `(row false, pt true)`. -/
def pa : Fin 2 → Carrier Bool Cb := rowPts true lab0 ![true]
def pb : Fin 2 → Carrier Bool Cb := rowPts false lab0 ![true]

theorem matched_pa_pb : Matched swap pa pb := by
  intro i
  fin_cases i
  · refine ⟨fun r => ?_, fun r τ => iff_of_false
      (not_inFiber_of_eq_row (a := pa) (i := 0) rfl r τ)
      (not_inFiber_of_eq_row (a := pb) (i := 0) rfl _ τ)⟩
    show Carrier.row true = Carrier.row r ↔ Carrier.row false = Carrier.row (swap r)
    cases r <;> simp [swap]
  · refine ⟨fun r => iff_of_false (fun h => by cases h) (fun h => by cases h), fun r τ => ?_⟩
    show InFiber pa r τ 1 ↔ InFiber pb (swap r) τ 1
    rw [inFiber_iff_of_eq_pt (a := pa) (i := 1) rfl, inFiber_iff_of_eq_pt (a := pb) (i := 1) rfl]
    cases r <;> simp [swap]

theorem fiberBF_pa_pb (α : Ordinal) : FiberBF Lc α swap matched_pa_pb := by
  intro r τ k ι hι
  have h : (fun j => matched_pa_pb.eltB (hι j)) = fun j => elt (hι j) := by
    funext j
    have hcase : ∀ i : Fin 2, ∀ r τ (h : InFiber pa r τ i),
        ∃ hr : r = true, ∃ hτ : τ = lab0, HEq (elt h) true ∧ HEq (matched_pa_pb.eltB h) true := by
      intro i r τ h
      fin_cases i
      · exact absurd h (not_inFiber_of_eq_row (a := pa) (i := 0) rfl r τ)
      · obtain ⟨rfl, rfl⟩ := (inFiber_iff_of_eq_pt (a := pa) (i := 1) rfl r τ).mp h
        exact ⟨rfl, rfl, heq_of_eq (elt_eq h rfl), heq_of_eq (matched_pa_pb.eltB_eq h rfl)⟩
    obtain ⟨rfl, rfl, h1, h2⟩ := hcase (ι j) r τ (hι j)
    exact (eq_of_heq h2).trans (eq_of_heq h1).symm
  rw [h]
  exact BFEquiv.refl α _

/-- The assembled pointed tuples are equivalent at level `1`. -/
theorem assembled_one : BFEquiv (L := lang ℕ Lc) 1 2 pa pb :=
  bfEquiv_of_fiberBF 1 matched_pa_pb (fiberBF_pa_pb 1)

/-- **Restriction at a successor level**: the component points are `BFEquiv 1`. -/
theorem restriction_succ_regression :
    BFEquiv (L := Lc) 1 1 (![true] : Fin 1 → Cb true lab0) (![true] : Fin 1 → Cb false lab0) :=
  bfEquiv_restrict_pointed 1 lab0 assembled_one

/-! ### Negative, level zero, empty fiber, nullary fact -/

/-- Fibers `Unit` at row `true`, `Empty` at row `false`. -/
def Cue : Bool → Label ℕ → Type
  | true, _ => Unit
  | false, _ => Empty

instance instCue : ∀ (r : Bool) (τ : Label ℕ), Lc.Structure (Cue r τ)
  | true, _ => inferInstanceAs (Lc.Structure Unit)
  | false, _ => inferInstanceAs (Lc.Structure Empty)

/-- The fibers of the two rows are not even level-`0` equivalent: `c` fails in `Unit` and holds
in `Empty`, an empty fiber. -/
theorem fibers_not_zero :
    ¬ BFEquiv (L := Lc) 0 0 (Fin.elim0 : Fin 0 → Cue true lab0)
      (Fin.elim0 : Fin 0 → Cue false lab0) := by
  intro h
  have h0 := (BFEquiv.zero _ _).mp h (AtomicIdx.rel CSym.c Fin.elim0)
  simp only [AtomicIdx.holds] at h0
  exact (show ¬ @Structure.RelMap Lc (Cue true lab0) _ 0 CSym.c _ from id) (h0.mpr trivial)

/-- **Lifted nullary facts distinguish rows at level zero**: the rows are not `BFEquiv 0` in the
assembled language, by the contrapositive of the empty-tuple corollary, with no fiber point. -/
theorem rows_not_zero_regression :
    ¬ BFEquiv (L := lang ℕ Lc) 0 1 ![(Carrier.row true : Carrier Bool Cue)]
      ![(Carrier.row false : Carrier Bool Cue)] :=
  fun h => fibers_not_zero (bfEquiv_restrict_nil 0 h lab0)

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.FiberAssembly.exists_pt_of_bfEquiv_snoc,
   `FirstOrder.Language.FiberAssembly.sameAtomicType_of_rowPts,
   `FirstOrder.Language.FiberAssembly.bfEquiv_restrict_pointed,
   `FirstOrder.Language.FiberAssembly.bfEquiv_restrict_nil,
   `matched_pa_pb, `fiberBF_pa_pb, `assembled_one, `restriction_succ_regression,
   `fibers_not_zero, `rows_not_zero_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "fiber BF-restriction regression guard: OK (successor-level restriction of an assembled \
    pointed tuple, level-zero non-equivalence of rows from an empty fiber's nullary fact; \
    headline declarations on standard axioms)"
