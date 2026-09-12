/-
Regression guard for the finite-tuple orbit bound (`ModelTheory/FiberOrbitBound.lean`).

A concrete instance where every hypothesis is discharged: `U = ℕ`, every letter allowed at every
position, the empty component language (relational), every component `Unit` (so every letter is
default-like, H_sep and H_up are immediate, and every fiber tuple has orbit rank `0`), and
`α = ω` (a nonzero limit, so `AddNatClosed ω`).  The rows `[1]` and `[2]` are swapped by a row
permutation `e`, and `g₀ := assemble e f` is the corresponding automorphism.

The **endpoint itself** (`exists_automorphism_bound`) is exercised on:

1. the empty tuple;
2. a tuple with **no row coordinate**, a **shared owner** `[1]`, and a **repeated point**, against
   the target `g₀ ∘ a`, which moves the owner row (so the owner-row step is genuinely used);
3. a single row `[1]` against the target row `[2]` (row movement);
4. the corollary `internalScottRank M ≤ ω`.

Targets in 2 and 3 differ from the sources.  Headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_fiber_orbit_bound_regressions.lean
-/
import InfinitaryLogic.ModelTheory.FiberOrbitBound
import Mathlib.Data.Fin.VecNotation

open Lean FirstOrder Language FiberAssembly

/-! ### The instance -/

instance : Language.empty.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

instance : Language.empty.Structure Unit := Language.emptyStructure

/-- All components are `Unit`. -/
abbrev Bu : ℕ → Type := fun _ => Unit

def Aall : ℕ → Set ℕ := fun _ => Set.univ

abbrev M := PrefixCarrier Unit Bu Aall

instance (o : Option ℕ) : Unique (Comp Unit Bu o) := by
  cases o <;> exact inferInstanceAs (Unique Unit)

instance (r : Row Aall) (τ : Label ℕ) : Unique (prefixFiber Unit Bu Aall r τ) :=
  inferInstanceAs (Unique (Comp Unit Bu (compIndex r.1 τ)))

/-- Tuples of a subsingleton structure have orbit rank `0`. -/
theorem orbitRank_eq_zero_of_subsingleton {L : Language} {N : Type} [L.Structure N]
    [Subsingleton N] {k : ℕ} (t : Fin k → N) : orbitRank (L := L) t = 0 := by
  apply le_antisymm _ _root_.zero_le
  apply orbitRank_le_of_mem
  intro b _ γ
  rw [show b = t from funext fun i => Subsingleton.elim _ _]
  exact BFEquiv.refl γ t

theorem sep_regression : SepBounded Language.empty Unit Bu Aall Ordinal.omega0 :=
  fun _ => ⟨0, Ordinal.omega0_pos, fun _ _ _ _ hu => absurd ⟨Language.Equiv.refl _ _⟩ hu⟩

theorem up_regression : UpwardClosed (DefaultLike Language.empty Unit Bu) :=
  fun _ _ => ⟨Language.Equiv.refl _ _⟩

theorem orb_regression : OrbitBounded Language.empty Unit Bu Aall Ordinal.omega0 :=
  fun _ _ _ t => by rw [orbitRank_eq_zero_of_subsingleton t]; exact Ordinal.omega0_pos

theorem closed_regression : AddNatClosed Ordinal.omega0 :=
  AddNatClosed.of_isSuccLimit Ordinal.isSuccLimit_omega0

/-! ### Rows, the swap, and the assembled automorphism -/

def row1 (u : ℕ) : Row Aall := ⟨[u], ⟨List.pairwise_singleton _ _, fun _ _ => Set.mem_univ _⟩⟩

theorem row1_ne : row1 1 ≠ row1 2 := fun h => by
  have := congrArg Subtype.val h
  simp [row1] at this

open Classical in
/-- The row permutation swapping `[1]` and `[2]`. -/
noncomputable def eswap : Row Aall ≃ Row Aall := Equiv.swap (row1 1) (row1 2)

/-- Fiber isomorphisms along the swap: all fibers are singletons. -/
noncomputable def fswap (t : Row Aall) (τ : Label ℕ) :
    prefixFiber Unit Bu Aall t τ ≃[Language.empty] prefixFiber Unit Bu Aall (eswap t) τ where
  toEquiv := Equiv.ofUnique _ _
  map_fun' := fun {_} f _ => Empty.elim f
  map_rel' := fun {_} R _ => Empty.elim R

/-- The assembled automorphism. -/
noncomputable def g₀ : M ≃[lang ℕ Language.empty] M := assemble eswap fswap

/-- A label. -/
def τa : Label ℕ := ⟨[1], by decide⟩

/-- Another label. -/
def τb : Label ℕ := ⟨[1, 1], by decide⟩

/-- **The endpoint on the empty tuple.** -/
theorem empty_tuple_regression :
    ∃ β < Ordinal.omega0.{0}, ∀ b : Fin 0 → M,
      BFEquiv (L := lang ℕ Language.empty) β 0 (Fin.elim0 : Fin 0 → M) b →
      ∃ g : M ≃[lang ℕ Language.empty] M, ⇑g ∘ (Fin.elim0 : Fin 0 → M) = b :=
  exists_automorphism_bound (Lc := Language.empty) (Bstar := Unit) (B := Bu) (A := Aall)
    Ordinal.omega0 sep_regression up_regression orb_regression closed_regression 0 Fin.elim0

/-- The source tuple of regression 2: no row, shared owner `[1]`, repeated point. -/
def a2 : Fin 3 → M :=
  ![Carrier.pt (row1 1) τa default, Carrier.pt (row1 1) τb default, Carrier.pt (row1 1) τa default]

/-- **The endpoint on a rowless tuple with a shared owner and a repeated point**, against a
target moving the owner row. -/
theorem rowless_regression :
    (⇑g₀ ∘ a2) 0 ≠ a2 0 ∧
    ∃ g : M ≃[lang ℕ Language.empty] M, ⇑g ∘ a2 = ⇑g₀ ∘ a2 := by
  refine ⟨fun h => ?_, ?_⟩
  · have : Carrier.pt (eswap (row1 1)) τa (fswap (row1 1) τa default) =
        Carrier.pt (row1 1) τa default := h
    have hr := (Carrier.pt.inj this).1
    rw [eswap, Equiv.swap_apply_left] at hr
    exact row1_ne hr.symm
  · obtain ⟨β, -, hβ⟩ := exists_automorphism_bound (Lc := Language.empty) (Bstar := Unit)
      (B := Bu) (A := Aall) Ordinal.omega0 sep_regression up_regression orb_regression
      closed_regression 3 a2
    exact hβ _ (bfEquiv_all_of_automorphism g₀ rfl β)

/-- **The endpoint on a single row**, against a different row. -/
theorem row_move_regression :
    (⇑g₀ ∘ ![(Carrier.row (row1 1) : M)]) 0 ≠ Carrier.row (row1 1) ∧
    ∃ g : M ≃[lang ℕ Language.empty] M,
      ⇑g ∘ ![(Carrier.row (row1 1) : M)] = ⇑g₀ ∘ ![(Carrier.row (row1 1) : M)] := by
  refine ⟨fun h => ?_, ?_⟩
  · have : Carrier.row (eswap (row1 1)) = (Carrier.row (row1 1) : M) := h
    have hr := Carrier.row.inj this
    rw [eswap, Equiv.swap_apply_left] at hr
    exact row1_ne hr.symm
  · obtain ⟨β, -, hβ⟩ := exists_automorphism_bound (Lc := Language.empty) (Bstar := Unit)
      (B := Bu) (A := Aall) Ordinal.omega0 sep_regression up_regression orb_regression
      closed_regression 1 ![Carrier.row (row1 1)]
    exact hβ _ (bfEquiv_all_of_automorphism g₀ rfl β)

/-- **The internal Scott rank corollary.** -/
theorem scottRank_regression :
    internalScottRank (L := lang ℕ Language.empty) M ≤ Ordinal.omega0 :=
  internalScottRank_le_of_bounds (Lc := Language.empty) (Bstar := Unit) (B := Bu) (A := Aall)
    Ordinal.omega0 sep_regression up_regression orb_regression closed_regression

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.FiberAssembly.exists_automorphism_bound,
   `FirstOrder.Language.FiberAssembly.internalScottRank_le_of_bounds,
   `FirstOrder.Language.FiberAssembly.matched_of_sameAtomicType_ownerRows,
   `FirstOrder.Language.FiberAssembly.owners_present_append_ownerRows,
   `FirstOrder.Language.FiberAssembly.AddNatClosed.of_isSuccLimit,
   `empty_tuple_regression, `rowless_regression, `row_move_regression, `scottRank_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "fiber orbit-bound regression guard: OK (endpoint on the empty tuple, on a rowless tuple \
    with a shared owner and a repeated point against a row-moving target, on a single moved row, \
    and the internal Scott rank corollary; headline declarations on standard axioms)"
