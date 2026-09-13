/-
Regression guard for the conditional exact rank (`ModelTheory/FiberExactRank.lean`).

Reuses the two-row instance: `U = ℕ`, nested allowed sets `A n = {m | m ≤ n}`, the row
`p = [0]`, component language with one binary symbol, default component `Unit` and components
`Bool`, equivalent at level `0` as structures but not isomorphic.

Checked: **cofinal approximation at `α = 1`** is discharged concretely (below `1` only level `0`
occurs, witnessed by the row `[0]`), and the **lower-bound endpoint** gives
`1 ≤ internalScottRank`; this instance tests only the lower theorem, since `AddNatClosed 1` is
false.  The **equality endpoint** is exercised as a **conditional composition regression**: its
original hypotheses are taken as parameters and the endpoint applied, on this instance's types;
it is not a concrete exact-rank example.  Headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_fiber_exact_rank_regressions.lean
-/
import InfinitaryLogic.ModelTheory.FiberExactRank
import Mathlib.Data.Fin.VecNotation

open Lean FirstOrder Language FiberAssembly

/-- The component language: one binary symbol. -/
inductive CSym : ℕ → Type
  | e : CSym 2

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

abbrev M := PrefixCarrier Unit Bfam Aiic

/-- **Cofinal approximation at `α = 1`**, discharged concretely by the row `[0]`. -/
theorem cofinal_regression : CofinalApprox Lc Unit Bfam Aiic 1 := by
  intro β hβ
  obtain rfl := Order.lt_one_iff.mp hβ
  exact ⟨p0, p0_ne, level_zero_regression, not_iso_regression⟩

/-- **The lower-bound endpoint** on the two-row instance. -/
theorem lower_regression : (1 : Ordinal) ≤ internalScottRank (L := lang ℕ Lc) M :=
  le_internalScottRank_of_cofinalApprox (Bstar := Unit) (B := Bfam) nested_regression 1
    cofinal_regression

/-- **Conditional composition regression**: the equality endpoint applied on this instance's
types with its original hypotheses as parameters.  Not a concrete exact-rank example: on this
instance `AddNatClosed 1` is false, and no `α` is claimed. -/
theorem conditional_composition_regression (α : Ordinal) (hsep : SepBounded Lc Unit Bfam Aiic α)
    (hup : UpwardClosed (DefaultLike Lc Unit Bfam)) (horb : OrbitBounded Lc Unit Bfam Aiic α)
    (hα : AddNatClosed α) (hcof : CofinalApprox Lc Unit Bfam Aiic α) :
    internalScottRank (L := lang ℕ Lc) M = α :=
  internalScottRank_eq_of_bounds nested_regression α hsep hup horb hα hcof

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.FiberAssembly.le_internalScottRank_of_cofinalApprox,
   `FirstOrder.Language.FiberAssembly.internalScottRank_eq_of_bounds,
   `cofinal_regression, `lower_regression, `conditional_composition_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "fiber exact-rank regression guard: OK (cofinal approximation at alpha = 1 discharged, \
    lower-bound endpoint, conditional composition of the equality endpoint; headline \
    declarations on standard axioms)"
