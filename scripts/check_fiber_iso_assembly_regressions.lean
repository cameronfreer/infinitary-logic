/-
Regression guard for isomorphism assembly and restriction on row assemblies
(`ModelTheory/FiberIsoAssembly.lean`).

Generic core with two rows (`Bool`).  Checked: the exact interpretation equivalences on
canonical fiber points; assembly from a row swap and identity component isomorphisms, with its
computation on rows and points; restriction of the assembled isomorphism back to the swap
(`restrictRows_assemble`) and to the supplied fiber maps at the carrier level; restriction of a
**nullary fact at an empty fiber** (the fiber of one row is `Empty` and the nullary symbol holds
there), which needs no fiber point; and the row bijection carries no order-preservation
requirement (the swap reverses the order of `Bool`).  Headline declarations use only the
standard axioms.

Run with: lake env lean scripts/check_fiber_iso_assembly_regressions.lean
-/
import InfinitaryLogic.ModelTheory.FiberIsoAssembly

open Lean FirstOrder Language FiberAssembly

/-- The component language: one binary symbol `e`, one nullary symbol `c`. -/
inductive CSym : ℕ → Type
  | e : CSym 2
  | c : CSym 0

/-- The component language, relational. -/
abbrev Lc : Language := ⟨fun _ => Empty, CSym⟩

instance : Lc.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

/-- The empty component: the nullary symbol holds there. -/
instance instEmptyC : Lc.Structure Empty where
  funMap f _ := (f : Empty).elim
  RelMap {n} R _ := match n, R with
    | _, CSym.e => False
    | _, CSym.c => True

/-- The component `Bool`: `e` is inequality, `c` fails. -/
instance instBoolC : Lc.Structure Bool where
  funMap f _ := (f : Empty).elim
  RelMap {n} R v := match n, R with
    | _, CSym.e => v 0 ≠ v 1
    | _, CSym.c => False

/-- A label. -/
def lab0 : Label ℕ := ⟨[0], by decide⟩

/-! ### A symmetric family: both rows carry `Bool` fibers; the row swap assembles -/

/-- Constant fiber family. -/
abbrev Cb : Bool → Label ℕ → Type := fun _ _ => Bool

/-- The row swap, which reverses the order of `Bool`: no order-preservation is required. -/
def swap : Bool ≃ Bool := ⟨not, not, Bool.not_not, Bool.not_not⟩

/-- Identity component isomorphisms. -/
def fid : ∀ (r : Bool) (τ : Label ℕ), Cb r τ ≃[Lc] Cb (swap r) τ :=
  fun _ _ => Language.Equiv.refl Lc Bool

/-- The assembled isomorphism of the swap. -/
noncomputable def gswap : Carrier Bool Cb ≃[lang ℕ Lc] Carrier Bool Cb := assemble swap fid

/-- Computation on rows and points. -/
theorem assemble_computation_regression :
    gswap (Carrier.row true) = Carrier.row false ∧
    gswap (Carrier.pt true lab0 true) = Carrier.pt false lab0 true :=
  ⟨rfl, rfl⟩

/-- Restriction to rows returns the swap. -/
theorem restrictRows_regression : restrictRows gswap = swap :=
  restrictRows_assemble swap fid

/-- Restriction to fibers returns the supplied component isomorphism, at the carrier level. -/
theorem restrictFiber_regression (x : Bool) :
    Carrier.pt (restrictRows gswap true) lab0 (restrictFiber gswap true lab0 x) =
      (Carrier.pt false lab0 x : Carrier Bool Cb) :=
  restrictFiber_assemble_pt swap fid true lab0 x

/-- Exact interpretation on canonical fiber points: the lifted binary symbol is inequality. -/
theorem exact_lift_regression :
    Structure.RelMap (L := lang ℕ Lc) (Sym.lift CSym.e)
      (fun i => (Carrier.pt true lab0 (![true, false] i) : Carrier Bool Cb)) ∧
    ¬ Structure.RelMap (L := lang ℕ Lc) (Sym.lift CSym.e)
      (fun i => (Carrier.pt true lab0 (![true, true] i) : Carrier Bool Cb)) := by
  refine ⟨(relMap_lift_pt (Lc := Lc) (C := Cb) CSym.e true lab0 ![true, false]).mpr ?_, fun h => ?_⟩
  · show (true : Bool) ≠ false
    decide
  · have := (relMap_lift_pt (Lc := Lc) (C := Cb) CSym.e true lab0 ![true, true]).mp h
    exact this rfl

/-- Exact interpretation of `own` and `lab` on canonical points. -/
theorem exact_own_lab_regression :
    Structure.RelMap (L := lang ℕ Lc) Sym.own
      ![(Carrier.pt true lab0 true : Carrier Bool Cb), Carrier.row true] ∧
    ¬ Structure.RelMap (L := lang ℕ Lc) Sym.own
      ![(Carrier.pt true lab0 true : Carrier Bool Cb), Carrier.row false] ∧
    Structure.RelMap (L := lang ℕ Lc) (Sym.lab lab0)
      ![(Carrier.pt true lab0 true : Carrier Bool Cb)] :=
  ⟨(relMap_own_pt (C := Cb) true true lab0 true).mpr rfl,
    fun h => Bool.false_ne_true ((relMap_own_pt (C := Cb) true false lab0 true).mp h),
    (relMap_lab_pt (C := Cb) lab0 true lab0 true).mpr rfl⟩

/-! ### An asymmetric family: one row has empty fibers; nullary facts still restrict -/

/-- Fibers `Bool` at row `true`, `Empty` at row `false`. -/
def Ce : Bool → Label ℕ → Type
  | true, _ => Bool
  | false, _ => Empty

instance instCe : ∀ (r : Bool) (τ : Label ℕ), Lc.Structure (Ce r τ)
  | true, _ => inferInstanceAs (Lc.Structure Bool)
  | false, _ => inferInstanceAs (Lc.Structure Empty)

/-- The identity assembly on the asymmetric family. -/
noncomputable def gid : Carrier Bool Ce ≃[lang ℕ Lc] Carrier Bool Ce :=
  assemble (Equiv.refl Bool) (fun r τ => Language.Equiv.refl Lc (Ce r τ))

/-- The fiber of row `false` is empty. -/
theorem empty_fiber_regression : IsEmpty (Ce false lab0) := inferInstanceAs (IsEmpty Empty)

/-- **A nullary fact at an empty fiber restricts along an assembled isomorphism**: `c` holds in
the empty fiber of row `false`, and `restrict_lift0` transports it to the image fiber, with no
fiber point anywhere. -/
theorem nullary_restrict_regression :
    @Structure.RelMap Lc (Ce (restrictRows gid false) lab0) _ 0 CSym.c Fin.elim0 :=
  (restrict_lift0 gid false lab0 CSym.c).mp (show True from trivial)

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.FiberAssembly.relMap_lift_pt,
   `FirstOrder.Language.FiberAssembly.relMap_own_pt,
   `FirstOrder.Language.FiberAssembly.relMap_lab_pt,
   `FirstOrder.Language.FiberAssembly.assemble, `FirstOrder.Language.FiberAssembly.assemble_row,
   `FirstOrder.Language.FiberAssembly.assemble_pt,
   `FirstOrder.Language.FiberAssembly.restrictRows,
   `FirstOrder.Language.FiberAssembly.restrictRows_apply,
   `FirstOrder.Language.FiberAssembly.restrictFiber,
   `FirstOrder.Language.FiberAssembly.restrictFiber_apply,
   `FirstOrder.Language.FiberAssembly.restrict_lift0,
   `FirstOrder.Language.FiberAssembly.restrictRows_assemble,
   `FirstOrder.Language.FiberAssembly.restrictFiber_assemble_pt,
   `assemble_computation_regression, `restrictRows_regression, `restrictFiber_regression,
   `exact_lift_regression, `exact_own_lab_regression, `empty_fiber_regression,
   `nullary_restrict_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "fiber iso-assembly regression guard: OK (exact interpretation on canonical points, \
    assembly of a row swap with computation on rows and points, restriction round trips, nullary \
    fact restricted at an empty fiber; headline declarations on standard axioms)"
