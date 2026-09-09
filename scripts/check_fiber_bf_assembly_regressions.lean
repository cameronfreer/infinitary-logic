/-
Regression guard for back-and-forth assembly under a fixed row bijection
(`ModelTheory/FiberBFAssembly.lean`) and for `BFEquiv.relabel` (`Scott/BFEquivRelabel.lean`).

Two rows (`Bool`), constant `Bool` fibers, the row swap as the fixed bijection.  Checked: a
tuple with a row coordinate and a **repeated** fiber-point coordinate is matched to its image;
level-`α` fiber data assemble to level-`α` equivalence of the tuples for **every** `α` (the same
level, no cost for the row coordinate); the fiber data contain the empty tuple of an
**unoccupied** fiber; the theorem applies directly to a tuple of repeated fiber points whose owner
is **absent** and to the empty tuples; and relabeling by a repetition and by a sub-selection
preserves `BFEquiv`.
Headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_fiber_bf_assembly_regressions.lean
-/
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

/-- Two labels. -/
def lab0 : Label ℕ := ⟨[0], by decide⟩
def lab1 : Label ℕ := ⟨[1], by decide⟩

/-- Constant fiber family. -/
abbrev Cb : Bool → Label ℕ → Type := fun _ _ => Bool

/-- The row swap. -/
def swap : Bool ≃ Bool := ⟨not, not, Bool.not_not, Bool.not_not⟩

/-- A tuple: a fiber point, a row, and the **same** fiber point again. -/
def ta : Fin 3 → Carrier Bool Cb :=
  ![Carrier.pt true lab0 true, Carrier.row true, Carrier.pt true lab0 true]

/-- Its image under the swap. -/
def tb : Fin 3 → Carrier Bool Cb :=
  ![Carrier.pt false lab0 true, Carrier.row false, Carrier.pt false lab0 true]

/-- The tuples are matched along the swap. -/
theorem matched_regression : Matched swap ta tb := by
  intro i
  fin_cases i
  · refine ⟨fun r => iff_of_false (fun h => by cases h) (fun h => by cases h), fun r τ => ?_⟩
    show InFiber ta r τ 0 ↔ InFiber tb (swap r) τ 0
    rw [inFiber_iff_of_eq_pt (a := ta) (i := 0) rfl, inFiber_iff_of_eq_pt (a := tb) (i := 0) rfl]
    cases r <;> simp [swap]
  · refine ⟨fun r => ?_, fun r τ => iff_of_false (not_inFiber_of_eq_row (a := ta) (i := 1) rfl r τ)
      (not_inFiber_of_eq_row (a := tb) (i := 1) rfl _ τ)⟩
    show Carrier.row true = Carrier.row r ↔ Carrier.row false = Carrier.row (swap r)
    cases r <;> simp [swap]
  · refine ⟨fun r => iff_of_false (fun h => by cases h) (fun h => by cases h), fun r τ => ?_⟩
    show InFiber ta r τ 2 ↔ InFiber tb (swap r) τ 2
    rw [inFiber_iff_of_eq_pt (a := ta) (i := 2) rfl, inFiber_iff_of_eq_pt (a := tb) (i := 2) rfl]
    cases r <;> simp [swap]

/-- Every fiber selection has identical component tuples on the two sides (both sides read
`true` at every fiber coordinate), so the fiber data hold at every level. -/
theorem fiberBF_regression (α : Ordinal) : FiberBF Lc α swap matched_regression := by
  intro r τ k ι hι
  have h : (fun j => matched_regression.eltB (hι j)) = fun j => elt (hι j) := by
    funext j
    -- both coordinates carry the value `true`
    have hcase : ∀ i : Fin 3, ∀ r τ (h : InFiber ta r τ i),
        ∃ hr : r = true, ∃ hτ : τ = lab0, HEq (elt h) true ∧
          HEq (matched_regression.eltB h) true := by
      intro i r τ h
      fin_cases i
      · obtain ⟨rfl, rfl⟩ := (inFiber_iff_of_eq_pt (a := ta) (i := 0) rfl r τ).mp h
        exact ⟨rfl, rfl, heq_of_eq (elt_eq h rfl), heq_of_eq (matched_regression.eltB_eq h rfl)⟩
      · exact absurd h (not_inFiber_of_eq_row (a := ta) (i := 1) rfl r τ)
      · obtain ⟨rfl, rfl⟩ := (inFiber_iff_of_eq_pt (a := ta) (i := 2) rfl r τ).mp h
        exact ⟨rfl, rfl, heq_of_eq (elt_eq h rfl), heq_of_eq (matched_regression.eltB_eq h rfl)⟩
    obtain ⟨rfl, rfl, h1, h2⟩ := hcase (ι j) r τ (hι j)
    exact (eq_of_heq h2).trans (eq_of_heq h1).symm
  rw [h]
  exact BFEquiv.refl α _

/-- **Assembly at the same level**: the matched tuples are back-and-forth equivalent at every
level `α` in the assembled language, with no level spent on the row coordinate. -/
theorem assembly_regression (α : Ordinal) : BFEquiv (L := lang ℕ Lc) α 3 ta tb :=
  bfEquiv_of_fiberBF α matched_regression (fiberBF_regression α)

/-- **Unoccupied fibers are part of the data**: the fiber `(false, lab1)` holds no coordinate of
`ta`, and the fiber data still assert the equivalence of its empty tuples. -/
theorem unoccupied_fiber_regression (α : Ordinal) :
    BFEquiv (L := Lc) α 0 (Fin.elim0 : Fin 0 → Cb false lab1)
      (Fin.elim0 : Fin 0 → Cb false lab1) := by
  have h := fiberBF_regression α false lab1 0 Fin.elim0 (fun j => j.elim0)
  rwa [show (fun j : Fin 0 => elt (show InFiber ta false lab1 (Fin.elim0 j) from j.elim0)) =
      Fin.elim0 from funext fun j => j.elim0,
    show (fun j : Fin 0 => matched_regression.eltB
      (show InFiber ta false lab1 (Fin.elim0 j) from j.elim0)) = Fin.elim0 from
      funext fun j => j.elim0] at h

/-- No coordinate of `ta` lies in the fiber `(false, lab1)`. -/
theorem unoccupied_regression (i : Fin 3) : ¬ InFiber ta false lab1 i := by
  fin_cases i
  · show ¬ InFiber ta false lab1 0
    rw [inFiber_iff_of_eq_pt (a := ta) (i := 0) rfl]; simp
  · exact not_inFiber_of_eq_row (a := ta) (i := 1) rfl _ _
  · show ¬ InFiber ta false lab1 2
    rw [inFiber_iff_of_eq_pt (a := ta) (i := 2) rfl]; simp

/-! ### Absent owner: a tuple of repeated fiber points only -/

/-- A tuple of the **same** fiber point twice; its owner row is absent from the tuple. -/
def ua : Fin 2 → Carrier Bool Cb := ![Carrier.pt true lab0 true, Carrier.pt true lab0 true]

/-- Its image under the swap. -/
def ub : Fin 2 → Carrier Bool Cb := ![Carrier.pt false lab0 true, Carrier.pt false lab0 true]

theorem matched_absent_owner : Matched swap ua ub := by
  intro i
  fin_cases i
  · refine ⟨fun r => iff_of_false (fun h => by cases h) (fun h => by cases h), fun r τ => ?_⟩
    show InFiber ua r τ 0 ↔ InFiber ub (swap r) τ 0
    rw [inFiber_iff_of_eq_pt (a := ua) (i := 0) rfl, inFiber_iff_of_eq_pt (a := ub) (i := 0) rfl]
    cases r <;> simp [swap]
  · refine ⟨fun r => iff_of_false (fun h => by cases h) (fun h => by cases h), fun r τ => ?_⟩
    show InFiber ua r τ 1 ↔ InFiber ub (swap r) τ 1
    rw [inFiber_iff_of_eq_pt (a := ua) (i := 1) rfl, inFiber_iff_of_eq_pt (a := ub) (i := 1) rfl]
    cases r <;> simp [swap]

theorem fiberBF_absent_owner (α : Ordinal) : FiberBF Lc α swap matched_absent_owner := by
  intro r τ k ι hι
  have h : (fun j => matched_absent_owner.eltB (hι j)) = fun j => elt (hι j) := by
    funext j
    have hcase : ∀ i : Fin 2, ∀ r τ (h : InFiber ua r τ i),
        ∃ hr : r = true, ∃ hτ : τ = lab0, HEq (elt h) true ∧
          HEq (matched_absent_owner.eltB h) true := by
      intro i r τ h
      fin_cases i
      · obtain ⟨rfl, rfl⟩ := (inFiber_iff_of_eq_pt (a := ua) (i := 0) rfl r τ).mp h
        exact ⟨rfl, rfl, heq_of_eq (elt_eq h rfl), heq_of_eq (matched_absent_owner.eltB_eq h rfl)⟩
      · obtain ⟨rfl, rfl⟩ := (inFiber_iff_of_eq_pt (a := ua) (i := 1) rfl r τ).mp h
        exact ⟨rfl, rfl, heq_of_eq (elt_eq h rfl), heq_of_eq (matched_absent_owner.eltB_eq h rfl)⟩
    obtain ⟨rfl, rfl, h1, h2⟩ := hcase (ι j) r τ (hι j)
    exact (eq_of_heq h2).trans (eq_of_heq h1).symm
  rw [h]
  exact BFEquiv.refl α _

/-- **Absent owner**: the theorem applied directly to a tuple of repeated fiber points whose
owner row is not in the tuple. -/
theorem absent_owner_regression (α : Ordinal) : BFEquiv (L := lang ℕ Lc) α 2 ua ub :=
  bfEquiv_of_fiberBF α matched_absent_owner (fiberBF_absent_owner α)

/-! ### Arity zero -/

theorem matched_nil : Matched swap (Fin.elim0 : Fin 0 → Carrier Bool Cb)
    (Fin.elim0 : Fin 0 → Carrier Bool Cb) :=
  fun i => i.elim0

theorem fiberBF_nil (α : Ordinal) : FiberBF Lc α swap matched_nil := by
  intro r τ k ι hι
  cases k with
  | zero =>
    have h : (fun j : Fin 0 => matched_nil.eltB (hι j)) = fun j => elt (hι j) :=
      funext fun j => j.elim0
    rw [h]
    exact BFEquiv.refl α _
  | succ k => exact (ι 0).elim0

/-- **Arity zero**: the theorem applied directly to the empty tuples. -/
theorem arity_zero_regression (α : Ordinal) :
    BFEquiv (L := lang ℕ Lc) α 0 (Fin.elim0 : Fin 0 → Carrier Bool Cb)
      (Fin.elim0 : Fin 0 → Carrier Bool Cb) :=
  bfEquiv_of_fiberBF α matched_nil (fiberBF_nil α)

/-- Relabeling by a repetition and by a sub-selection preserves `BFEquiv`. -/
theorem relabel_regression (α : Ordinal) :
    BFEquiv (L := lang ℕ Lc) α 4 (ta ∘ ![0, 0, 2, 1]) (tb ∘ ![0, 0, 2, 1]) ∧
    BFEquiv (L := lang ℕ Lc) α 1 (ta ∘ ![1]) (tb ∘ ![1]) :=
  ⟨BFEquiv.relabel α (assembly_regression α) _, BFEquiv.relabel α (assembly_regression α) _⟩

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.BFEquiv.relabel,
   `FirstOrder.Language.FiberAssembly.sameAtomicType_of_fiberBF_zero,
   `FirstOrder.Language.FiberAssembly.bfEquiv_of_fiberBF,
   `FirstOrder.Language.FiberAssembly.Matched.snoc_row,
   `FirstOrder.Language.FiberAssembly.Matched.snoc_pt,
   `matched_regression, `fiberBF_regression, `assembly_regression,
   `unoccupied_fiber_regression, `unoccupied_regression, `absent_owner_regression,
   `arity_zero_regression, `relabel_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "fiber BF-assembly regression guard: OK (matched tuple with a row and a repeated \
    point, fiber data at every level, same-level assembly, unoccupied fiber's empty tuple in the \
    data, absent owner and arity zero applied directly, relabeling by repetition and \
    sub-selection; headline declarations on standard axioms)"
