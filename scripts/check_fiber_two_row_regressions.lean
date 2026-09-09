/-
Regression guard for the two-row lower bound (`ModelTheory/FiberTwoRow.lean`).

A concrete nested instance: `U = ℕ`, allowed sets `A n = {m | m ≤ n}` (nested), the row
`p = [0]` and its extension `q = [0, 0]`; component language with one binary symbol; default
component `Unit` (the symbol fails) and components `Bool` (the symbol is inequality), which are
equivalent at level `0` as structures (no nullary atoms) but not isomorphic (cardinality).
Checked: `q` is an allowed row; the fibers of `p` and `q` agree away from the label `q` and
differ there (`B_*` against `B 0`); the two row elements are `BFEquiv 0` in the assembled
language, applied directly; no automorphism carries `p` to `q`; and, the assembled structure
being countable, the orbit rank of the row `p` is positive.  Headline declarations use only the
standard axioms.

Run with: lake env lean scripts/check_fiber_two_row_regressions.lean
-/
import InfinitaryLogic.ModelTheory.FiberTwoRow
import Mathlib.Data.Fin.VecNotation

open Lean FirstOrder Language FiberAssembly

/-- The component language: one binary symbol. -/
inductive CSym : ℕ → Type
  | e : CSym 2

/-- The component language, relational. -/
abbrev Lc : Language := ⟨fun _ => Empty, CSym⟩

instance : Lc.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

/-- The default component `Unit`: the symbol fails. -/
instance : Lc.Structure Unit where
  funMap f _ := (f : Empty).elim
  RelMap {n} R _ := match n, R with
    | _, CSym.e => False

/-- The components `Bool`: the symbol is inequality. -/
instance : Lc.Structure Bool where
  funMap f _ := (f : Empty).elim
  RelMap {n} R v := match n, R with
    | _, CSym.e => v 0 ≠ v 1

abbrev Bfam : ℕ → Type := fun _ => Bool

/-- Nested allowed sets: at position `n`, the letters `≤ n`. -/
def Aiic : ℕ → Set ℕ := fun n => Set.Iic n

theorem nested_regression : Nested Aiic := fun n _ hm => le_trans hm (Nat.le_succ n)

/-- The row `[0]`. -/
def p0 : Row Aiic := ⟨[0], by decide, fun i hi => by
  have : i = 0 := by simp at hi; omega
  subst this
  show (0 : ℕ) ∈ Set.Iic 0
  exact Set.mem_Iic.mpr le_rfl⟩

theorem p0_ne : p0.1 ≠ [] := by decide

/-- `q = [0, 0]` is an allowed row, and it is the extension of `p`. -/
theorem concatRow_regression : (concatRow nested_regression p0 p0_ne).1 = [0, 0] := rfl

/-- The fibers agree away from the label `q` and differ at it. -/
theorem fibers_regression :
    compIndex (concatRow nested_regression p0 p0_ne).1 ⟨[0], by decide⟩ =
      compIndex p0.1 ⟨[0], by decide⟩ ∧
    compIndex p0.1 (concatLabel p0.1 0) = none ∧
    compIndex (p0.1 ++ [0]) (concatLabel p0.1 0) = some 0 :=
  ⟨compIndex_concat_last_of_ne _ _ _ (by
      intro h
      have := congrArg Subtype.val h
      simp [concatLabel, p0] at this), compIndex_concat_label_of_shorter _ _,
    compIndex_concat_last_self _ _⟩

/-- `Unit` and `Bool` are equivalent at level `0` as structures: there are no nullary atoms. -/
theorem level_zero_regression :
    BFEquiv (L := Lc) 0 0 (Fin.elim0 : Fin 0 → Unit) (Fin.elim0 : Fin 0 → Bool) := by
  rw [BFEquiv.zero]
  intro idx
  cases idx with
  | eq i j => exact i.elim0
  | rel R f => cases R; exact (f 0).elim0

/-- `Unit` and `Bool` are not isomorphic. -/
theorem not_iso_regression : IsEmpty (Unit ≃[Lc] Bool) :=
  ⟨fun f => Bool.false_ne_true (f.symm.injective (Subsingleton.elim _ _))⟩

/-- **Two-row equivalence at level `0`, applied directly.** -/
theorem twoRow_bfEquiv_regression :
    BFEquiv (L := lang ℕ Lc) 0 1 (![(Carrier.row p0 : PrefixCarrier Unit Bfam Aiic)])
      (![(Carrier.row (concatRow nested_regression p0 p0_ne) : PrefixCarrier Unit Bfam Aiic)]) :=
  twoRow_bfEquiv nested_regression p0 p0_ne 0 level_zero_regression

/-- **No automorphism carries `p` to `q`.** -/
theorem twoRow_not_automorphic_regression :
    ¬ ∃ g : PrefixCarrier Unit Bfam Aiic ≃[lang ℕ Lc] PrefixCarrier Unit Bfam Aiic,
      g (Carrier.row p0) = Carrier.row (concatRow nested_regression p0 p0_ne) :=
  twoRow_not_automorphic nested_regression p0 p0_ne not_iso_regression

/-- The assembled structure is countable. -/
theorem countable_regression : Countable (PrefixCarrier Unit Bfam Aiic) := inferInstance

/-- **Orbit-rank corollary**: the orbit rank of the row `p` is positive. -/
theorem twoRow_orbitRank_regression :
    0 < orbitRank (L := lang ℕ Lc) (![(Carrier.row p0 : PrefixCarrier Unit Bfam Aiic)]) :=
  twoRow_lt_orbitRank nested_regression p0 p0_ne 0 level_zero_regression not_iso_regression

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.FiberAssembly.isAllowed_concat_last,
   `FirstOrder.Language.FiberAssembly.compIndex_concat_last_of_ne,
   `FirstOrder.Language.FiberAssembly.compIndex_concat_last_self,
   `FirstOrder.Language.FiberAssembly.compIndex_concat_label_of_shorter,
   `FirstOrder.Language.FiberAssembly.fiberBF_of_no_points,
   `FirstOrder.Language.FiberAssembly.twoRow_matched,
   `FirstOrder.Language.FiberAssembly.twoRow_bfEquiv,
   `FirstOrder.Language.FiberAssembly.twoRow_not_automorphic,
   `FirstOrder.Language.FiberAssembly.twoRow_lt_orbitRank,
   `FirstOrder.Language.FiberAssembly.instCountableCarrier,
   `nested_regression, `concatRow_regression, `fibers_regression, `level_zero_regression,
   `not_iso_regression, `twoRow_bfEquiv_regression, `twoRow_not_automorphic_regression,
   `countable_regression, `twoRow_orbitRank_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "fiber two-row regression guard: OK (nested allowed row extension, fiber agreement \
    away from the new label and difference at it, level-0 equivalence applied directly, \
    non-automorphism, positive orbit rank on a countable instance; headline declarations on \
    standard axioms)"
