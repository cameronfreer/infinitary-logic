/-
Regression guard for the labeled-fiber language and row assembly
(`ModelTheory/FiberAssembly.lean`).

A concrete instance: `U = ℕ`, every letter allowed, a component language with one binary and
one nullary symbol, default component `Unit` (nothing holds), components `Bool` (the binary
symbol is inequality, the nullary symbol holds).  Checked: the empty row and a two-letter row are
rows; a prefix label selects the component and a non-prefix label the default, by computation;
every symbol's interpretation equation on concrete points, including the owner-indexed lift of
the nullary symbol at a prefix label (true) and at a non-prefix label (false); lifted relations
are false on mixed-fiber tuples and on rows; symbol countability.  No `W` is mentioned anywhere.

Run with: lake env lean scripts/check_fiber_assembly_regressions.lean
-/
import InfinitaryLogic.ModelTheory.FiberAssembly
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

open Lean FirstOrder Language FiberAssembly

/-- The component language: one binary symbol `e`, one nullary symbol `c`. -/
inductive CSym : ℕ → Type
  | e : CSym 2
  | c : CSym 0

/-- The component language. -/
abbrev Lc : Language := ⟨fun _ => Empty, CSym⟩

instance : Countable (Σ n, CSym n) :=
  Function.Injective.countable (f := fun s : Σ n, CSym n => decide (s.1 = 2)) (by
    rintro ⟨_, s₁⟩ ⟨_, s₂⟩ h
    cases s₁ <;> cases s₂ <;> simp_all)

/-- The default component: nothing holds. -/
instance : Lc.Structure Unit where
  funMap f _ := (f : Empty).elim
  RelMap {n} R _ := match n, R with
    | _, CSym.e => False
    | _, CSym.c => False

/-- The components `B u = Bool`: `e` is inequality, `c` holds. -/
instance instB : Lc.Structure Bool where
  funMap f _ := (f : Empty).elim
  RelMap {n} R v := match n, R with
    | _, CSym.e => v 0 ≠ v 1
    | _, CSym.c => True

/-- Every letter is allowed at every position. -/
def Aall : ℕ → Set ℕ := fun _ => Set.univ

abbrev Bfam : ℕ → Type := fun _ => Bool

/-- The assembled carrier of the instance. -/
abbrev K : Type := Carrier Unit Bfam Aall

/-- The empty row. -/
def rowNil : Row Aall := ⟨[], isAllowed_nil _⟩

/-- The row `[3, 5]`. -/
def row35 : Row Aall := ⟨[3, 5], by decide, fun _ _ => Set.mem_univ _⟩

/-- The label `[3]`, a prefix of `[3, 5]`. -/
def lab3 : Label ℕ := ⟨[3], by decide⟩

/-- The label `[5]`, not a prefix of `[3, 5]`. -/
def lab5 : Label ℕ := ⟨[5], by decide⟩

/-- Prefix and non-prefix labels select the component and the default, by computation. -/
theorem compIndex_regression :
    compIndex row35.1 lab3 = some 3 ∧ compIndex row35.1 lab5 = none := by decide

/-- The row `[3, 5]` as a carrier element. -/
def r35 : K := Carrier.row row35

/-- The empty row as a carrier element. -/
def rNil : K := Carrier.row rowNil

/-- A point in the fiber of `[3, 5]` at label `[3]`: the fiber type reduces to `Bool`. -/
def pt3 (b : Bool) : K := Carrier.pt row35 lab3 (show Comp Unit Bfam (compIndex row35.1 lab3) from b)

/-- The point in the fiber of `[3, 5]` at label `[5]`: the fiber type reduces to `Unit`. -/
def pt5 : K := Carrier.pt row35 lab5 (show Comp Unit Bfam (compIndex row35.1 lab5) from ())

/-- Owner word of a carrier element. -/
def ownerWord : K → List ℕ
  | Carrier.row q => q.1
  | Carrier.pt q _ _ => q.1

/-- Label word of a carrier element (empty for rows). -/
def labelWord : K → List ℕ
  | Carrier.row _ => []
  | Carrier.pt _ τ _ => τ.1

section Equations

/-- `row` holds of a row and fails of a fiber point. -/
theorem row_regression :
    Structure.RelMap (L := lang ℕ Lc) Sym.row ![r35] ∧
    ¬ Structure.RelMap (L := lang ℕ Lc) Sym.row ![pt3 true] := by
  refine ⟨⟨row35, rfl⟩, ?_⟩
  rintro ⟨p, h⟩
  have := congrArg labelWord h
  simp [labelWord, pt3, lab3] at this

/-- `own` relates a fiber point to its row and not to another row. -/
theorem own_regression :
    Structure.RelMap (L := lang ℕ Lc) Sym.own ![pt3 true, r35] ∧
    ¬ Structure.RelMap (L := lang ℕ Lc) Sym.own ![pt3 true, rNil] := by
  refine ⟨⟨row35, lab3, _, rfl, rfl⟩, ?_⟩
  rintro ⟨p, τ, x, h1, h2⟩
  have e1 := congrArg ownerWord h1
  have e2 := congrArg ownerWord h2
  simp [ownerWord, pt3, row35, rNil, rowNil] at e1 e2
  rw [← e1] at e2
  cases e2

/-- `lab τ` holds exactly at label `τ`. -/
theorem lab_regression :
    Structure.RelMap (L := lang ℕ Lc) (Sym.lab lab3) ![pt3 true] ∧
    ¬ Structure.RelMap (L := lang ℕ Lc) (Sym.lab lab5) ![pt3 true] := by
  refine ⟨⟨row35, _, rfl⟩, ?_⟩
  rintro ⟨p, x, h⟩
  have := congrArg labelWord h
  simp [labelWord, pt3, lab3, lab5] at this

/-- The lifted binary symbol holds of two distinct points of one fiber (`e` is inequality in
`B 3 = Bool`). -/
theorem lift_regression :
    Structure.RelMap (L := lang ℕ Lc) (Sym.lift CSym.e) ![pt3 true, pt3 false] :=
  ⟨row35, lab3, ![show Comp Unit Bfam (compIndex row35.1 lab3) from true,
    show Comp Unit Bfam (compIndex row35.1 lab3) from false],
    fun i => by fin_cases i <;> rfl, show (true : Bool) ≠ false by decide⟩

/-- Lifted relations are false across fibers with different labels. -/
theorem lift_mixed_false_regression :
    ¬ Structure.RelMap (L := lang ℕ Lc) (Sym.lift CSym.e) ![pt3 true, pt5] := by
  intro h
  obtain ⟨p, τ, x, y, h0, h1⟩ :=
    @relMap_lift_same_fiber ℕ _ Lc Unit Bfam _ _ Aall 1 CSym.e _ h 0 1
  have e0 := congrArg labelWord h0
  have e1 := congrArg labelWord h1
  simp [labelWord, pt3, pt5, lab3, lab5] at e0 e1
  rw [← e0] at e1
  cases e1

/-- Lifted relations are false on a row argument. -/
theorem lift_row_false_regression :
    ¬ Structure.RelMap (L := lang ℕ Lc) (Sym.lift CSym.e) ![r35, pt3 true] :=
  @not_relMap_lift_of_row ℕ _ Lc Unit Bfam _ _ Aall 1 CSym.e _ 0 row35 rfl

/-- The owner-indexed lift of the nullary symbol: true at a prefix label (component `Bool`, where
`c` holds), false at a non-prefix label (default component, where nothing holds). -/
theorem lift0_regression :
    Structure.RelMap (L := lang ℕ Lc) (Sym.lift0 CSym.c lab3) ![r35] ∧
    ¬ Structure.RelMap (L := lang ℕ Lc) (Sym.lift0 CSym.c lab5) ![r35] := by
  refine ⟨⟨row35, rfl, show True from trivial⟩, ?_⟩
  rintro ⟨p, hp, hc⟩
  have e := congrArg ownerWord hp
  simp [ownerWord, r35] at e
  have hp' : p = row35 := Subtype.ext e.symm
  subst hp'
  exact (show False from hc)

end Equations

/-- Symbol countability for countable `U` and component symbols. -/
theorem countable_regression : Countable (Σ n, Sym ℕ Lc n) := inferInstance

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.FiberAssembly.relMap_row, `FirstOrder.Language.FiberAssembly.relMap_own,
   `FirstOrder.Language.FiberAssembly.relMap_lab, `FirstOrder.Language.FiberAssembly.relMap_lift,
   `FirstOrder.Language.FiberAssembly.relMap_lift0,
   `FirstOrder.Language.FiberAssembly.not_relMap_lift_of_row,
   `FirstOrder.Language.FiberAssembly.relMap_lift_same_fiber,
   `FirstOrder.Language.FiberAssembly.instCountableSigmaSym,
   `compIndex_regression, `row_regression, `own_regression, `lab_regression, `lift_regression,
   `lift_mixed_false_regression, `lift_row_false_regression, `lift0_regression,
   `countable_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "fiber-assembly regression guard: OK (rows incl. empty, prefix and non-prefix labels by \
    computation, every symbol's interpretation on concrete points, mixed-fiber and row \
    arguments false, owner-indexed nullary lift, symbol countability; headline declarations on \
    standard axioms)"
