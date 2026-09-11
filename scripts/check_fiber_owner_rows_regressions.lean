/-
Regression guard for owner rows at finite cost (`ModelTheory/FiberOwnerRows.lean`).

Reuses the two-row instance: `U = ℕ`, nested allowed sets `A n = {m | m ≤ n}`, the row
`p = [0]` and its extension `q = [0, 0]`, component language with one binary symbol, default
component `Unit` and components `Bool`, level-`0` equivalent as structures.

Checked: the **empty tuple** (owner rows of the empty tuple are empty, and the theorem applies
at `n = 0`); **repeated owners** (two points of the same row have the same owner row, and the
theorem applies to such a tuple); **already-present owners** (a point together with its own row;
the appended owner tuple repeats the row); and a **nontrivial application**: from the two-row
equivalence `row p ≡_{0+1} row q`, the owner-extended tuples `(row p, row p)` and
`(row q, row q)` are equivalent at level `0`.  Headline declarations use only the standard
axioms.

Run with: lake env lean scripts/check_fiber_owner_rows_regressions.lean
-/
import InfinitaryLogic.ModelTheory.FiberOwnerRows
import InfinitaryLogic.ModelTheory.FiberTwoRow
import Mathlib.Data.Fin.VecNotation

open Lean FirstOrder Language FiberAssembly

/-- The component language: one binary symbol. -/
inductive CSym : ℕ → Type
  | e : CSym 2

abbrev Lc : Language := ⟨fun _ => Empty, CSym⟩

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

/-- `Unit` and `Bool` are equivalent at level `0 + 1` as structures: any two points agree on the
binary symbol applied to a single point. -/
theorem level_one_regression :
    BFEquiv (L := Lc) (0 + ((1 : ℕ) : Ordinal)) 0 (Fin.elim0 : Fin 0 → Unit)
      (Fin.elim0 : Fin 0 → Bool) := by
  rw [Nat.cast_one, ← Order.succ_eq_add_one, BFEquiv.succ]
  refine ⟨level_zero_regression, fun _ => ⟨true, ?_⟩, fun _ => ⟨(), ?_⟩⟩ <;>
  · rw [BFEquiv.zero]
    intro idx
    have hone : ∀ i j : Fin (0 + 1), i = j := fun i j => Fin.ext (by omega)
    cases idx with
    | eq i j => rw [hone i j]; exact iff_of_true rfl rfl
    | rel R f =>
      cases R
      exact iff_of_false (fun h => (id h : False).elim)
        (fun h => h (by simp only [Function.comp_apply]; rw [hone (f 0) (f 1)]))

abbrev M := PrefixCarrier Unit Bfam Aiic

/-- **Empty tuple**: no owner rows, and the theorem applies at `n = 0`. -/
theorem empty_tuple_regression (β : Ordinal) :
    ownerRow (Fin.elim0 : Fin 0 → M) = Fin.elim0 ∧
    BFEquiv (L := lang ℕ Lc) β (0 + 0) (Fin.append (Fin.elim0 : Fin 0 → M) (ownerRow Fin.elim0))
      (Fin.append (Fin.elim0 : Fin 0 → M) (ownerRow Fin.elim0)) :=
  ⟨funext fun i => i.elim0, bfEquiv_append_ownerRows (BFEquiv.refl _ _)⟩

/-- **Repeated owners**: two points of the same row have the same owner row, and the theorem
applies to such a tuple. -/
theorem repeated_owners_regression (β : Ordinal) (τ τ' : Label ℕ)
    (x : prefixFiber Unit Bfam Aiic p0 τ) (y : prefixFiber Unit Bfam Aiic p0 τ') :
    ownerRow (![Carrier.pt p0 τ x, Carrier.pt p0 τ' y] : Fin 2 → M) =
      ![Carrier.row p0, Carrier.row p0] ∧
    BFEquiv (L := lang ℕ Lc) β (2 + 2)
      (Fin.append (![Carrier.pt p0 τ x, Carrier.pt p0 τ' y] : Fin 2 → M)
        ![Carrier.row p0, Carrier.row p0])
      (Fin.append (![Carrier.pt p0 τ x, Carrier.pt p0 τ' y] : Fin 2 → M)
        ![Carrier.row p0, Carrier.row p0]) := by
  have hown : ownerRow (![Carrier.pt p0 τ x, Carrier.pt p0 τ' y] : Fin 2 → M) =
      ![Carrier.row p0, Carrier.row p0] := by
    funext i
    fin_cases i <;> rfl
  refine ⟨hown, ?_⟩
  have h := bfEquiv_append_ownerRows
    (BFEquiv.refl (L := lang ℕ Lc) (β + ((2 : ℕ) : Ordinal))
      (![Carrier.pt p0 τ x, Carrier.pt p0 τ' y] : Fin 2 → M))
  rwa [hown] at h

/-- **Already-present owner**: a point together with its own row; the appended owner tuple
repeats the row. -/
theorem present_owner_regression (τ : Label ℕ) (x : prefixFiber Unit Bfam Aiic p0 τ) :
    ownerRow (![Carrier.pt p0 τ x, Carrier.row p0] : Fin 2 → M) =
      ![Carrier.row p0, Carrier.row p0] := by
  funext i
  fin_cases i <;> rfl

/-- **Nontrivial application**: from `row p ≡_{0+1} row q`, the owner-extended tuples are
equivalent at level `0`. -/
theorem two_row_owners_regression :
    BFEquiv (L := lang ℕ Lc) 0 (1 + 1)
      (Fin.append ![(Carrier.row p0 : M)] ![(Carrier.row p0 : M)])
      (Fin.append ![(Carrier.row (concatRow nested_regression p0 p0_ne) : M)]
        ![(Carrier.row (concatRow nested_regression p0 p0_ne) : M)]) := by
  have h := bfEquiv_append_ownerRows
    (twoRow_bfEquiv (Bstar := Unit) (B := Bfam) nested_regression p0 p0_ne
      (0 + ((1 : ℕ) : Ordinal)) level_one_regression)
  have h1 : ownerRow ![(Carrier.row p0 : M)] = ![(Carrier.row p0 : M)] := by
    funext i; fin_cases i; rfl
  have h2 : ownerRow ![(Carrier.row (concatRow nested_regression p0 p0_ne) : M)] =
      ![(Carrier.row (concatRow nested_regression p0 p0_ne) : M)] := by
    funext i; fin_cases i; rfl
  rwa [h1, h2] at h

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.FiberAssembly.bfEquiv_append_ownerRows,
   `level_one_regression, `empty_tuple_regression, `repeated_owners_regression,
   `present_owner_regression, `two_row_owners_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "fiber owner-rows regression guard: OK (empty tuple, repeated owners, already-present \
    owner, two-row application at level 0; headline declarations on standard axioms)"
