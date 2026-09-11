/-
Regression guard for the row-profile bound (`ModelTheory/FiberProfileBound.lean`).

A concrete instance over `U = ℕ`, every letter allowed at every position, with a component
language carrying one nullary relation `P`.  The default component `Bstar` is a point with `P`
false; the component `B u` is a point with `P` true exactly when `u < 5`.  So `B u` is
default-like iff `5 ≤ u`, the default-like letters are upward closed, and every non-default
component is separated from the default already at level `0` by the nullary atom: (H_sep) holds
with `α = 1` and a **genuine** non-default component (`B 1`).

Checked: the **empty row** (`ndPrefixes` is empty, and every fiber of the empty row is the
default); **different default tails** (`[7]` and `[9]` have the same non-default prefixes, so
their fibers are isomorphic at every label, via the label-by-label lemma); the **separation
bound** (`¬ BFEquiv 0 (B 1) Bstar`, (H_sep) at `α = 1`, and the endpoint forces `β = 0` and then
rules out `row [1] ≡_0 row []` because the fiber at `[1]` would be `B 1 ≅ Bstar`).  Headline
declarations use only the standard axioms.

Run with: lake env lean scripts/check_fiber_profile_bound_regressions.lean
-/
import InfinitaryLogic.ModelTheory.FiberProfileBound

open Lean FirstOrder Language FiberAssembly

/-! ### The component language: one nullary relation -/

inductive PSym : ℕ → Type
  | P : PSym 0

abbrev Lp : Language := ⟨fun _ => Empty, PSym⟩

/-- The default component: a point where `P` fails. -/
def Bstar0 : Type := Unit

instance : Lp.Structure Bstar0 where
  funMap {_} g _ := (g : Empty).elim
  RelMap {_} _ _ := False

/-- The components: a point where `P` holds exactly when `u < 5`. -/
def B0 (_u : ℕ) : Type := Unit

instance (u : ℕ) : Lp.Structure (B0 u) where
  funMap {_} g _ := (g : Empty).elim
  RelMap {_} _ _ := u < 5

/-- Every relation on `B0 u` says `u < 5`. -/
theorem relMap_B0 (u : ℕ) {n : ℕ} (R : Lp.Relations n) (v : Fin n → B0 u) :
    Structure.RelMap R v ↔ u < 5 :=
  Iff.rfl

/-- Every relation on `Bstar0` fails. -/
theorem relMap_Bstar0 {n : ℕ} (R : Lp.Relations n) (v : Fin n → Bstar0) :
    ¬ Structure.RelMap R v :=
  id

/-- Points of the components with `P` false are isomorphic to the default. -/
def toDefault (u : ℕ) (hu : 5 ≤ u) : B0 u ≃[Lp] Bstar0 where
  toEquiv := Equiv.refl Unit
  map_fun' := fun {_} g _ => (g : Empty).elim
  map_rel' := fun {_} R v =>
    ⟨fun h => (relMap_Bstar0 R _ h).elim,
      fun h => absurd hu (Nat.not_le.mpr ((relMap_B0 u R v).mp h))⟩

/-- Default-like exactly at `5 ≤ u`. -/
theorem defaultLike_iff (u : ℕ) : DefaultLike Lp Bstar0 B0 u ↔ 5 ≤ u := by
  constructor
  · rintro ⟨e⟩
    by_contra h
    exact relMap_Bstar0 PSym.P _
      ((e.map_rel PSym.P Fin.elim0).mpr ((relMap_B0 u _ _).mpr (Nat.not_le.mp h)))
  · exact fun hu => ⟨toDefault u hu⟩

theorem upward_regression : UpwardClosed (DefaultLike Lp Bstar0 B0) := by
  intro u v huv hu
  rw [defaultLike_iff] at hu ⊢
  exact hu.trans huv

/-! ### A genuine separation bound -/

/-- A non-default component is separated from the default at level `0`. -/
theorem not_bfEquiv_B0_one :
    ¬ BFEquiv (L := Lp) 0 0 (Fin.elim0 : Fin 0 → B0 1) (Fin.elim0 : Fin 0 → Bstar0) := by
  intro h
  have := (BFEquiv.zero _ _).mp h (AtomicIdx.rel PSym.P Fin.elim0)
  simp only [AtomicIdx.holds] at this
  exact relMap_Bstar0 PSym.P _ (this.mp ((relMap_B0 1 _ _).mpr (by decide)))

/-- Every letter is allowed everywhere. -/
def Aall : ℕ → Set ℕ := fun _ => Set.univ

/-- (H_sep) with `α = 1`: level `0` separates every non-default component. -/
theorem sepBounded_regression : SepBounded Lp Bstar0 B0 Aall 1 := by
  intro N
  refine ⟨0, zero_lt_one, fun n _ u _ hu h => ?_⟩
  rw [defaultLike_iff] at hu
  have := (BFEquiv.zero _ _).mp h (AtomicIdx.rel PSym.P Fin.elim0)
  simp only [AtomicIdx.holds] at this
  exact relMap_Bstar0 PSym.P _ (this.mp ((relMap_B0 u _ _).mpr (Nat.not_le.mp hu)))

/-! ### Rows -/

/-- A one-letter allowed row. -/
def row1 (u : ℕ) : Row Aall := ⟨[u], ⟨List.pairwise_singleton _ _, fun _ _ => Set.mem_univ _⟩⟩

/-- The empty row. -/
def row0 : Row Aall := ⟨[], isAllowed_nil _⟩

/-- **Empty row**: no non-default prefixes, and every fiber is the default component. -/
theorem empty_row_regression :
    ndPrefixes (DefaultLike Lp Bstar0 B0) row0.1 = ∅ ∧
    ∀ τ : Label ℕ, compIndex row0.1 τ = none := by
  refine ⟨?_, fun τ => compIndex_of_not_prefix fun h => τ.2 (List.prefix_nil.mp h)⟩
  ext τ
  simp only [mem_ndPrefixes, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun h => absurd (List.prefix_nil.mp h) τ.2

/-- **Different default tails, identical profiles**: `[7]` and `[9]` have no non-default
prefixes, so their fibers are isomorphic at every label. -/
theorem default_tails_regression :
    ndPrefixes (DefaultLike Lp Bstar0 B0) (row1 7).1 =
      ndPrefixes (DefaultLike Lp Bstar0 B0) (row1 9).1 ∧
    ∀ τ : Label ℕ,
      Nonempty (prefixFiber Bstar0 B0 Aall (row1 7) τ ≃[Lp] prefixFiber Bstar0 B0 Aall (row1 9) τ) := by
  have hnd : ∀ u, 5 ≤ u → ndPrefixes (DefaultLike Lp Bstar0 B0) (row1 u).1 = ∅ := by
    intro u hu
    ext τ
    simp only [mem_ndPrefixes, Set.mem_empty_iff_false, iff_false, not_and, not_not]
    intro h
    have : τ.last = u := by
      have hlen : τ.1.length = 1 := le_antisymm h.length_le (List.length_pos_of_ne_nil τ.2)
      have hτ : τ.1 = [u] := h.eq_of_length hlen
      have hmem : τ.last ∈ τ.1 := List.getLast_mem _
      rw [hτ] at hmem
      exact List.mem_singleton.mp hmem
    rw [this, defaultLike_iff]
    exact hu
  have h := (hnd 7 (by decide)).trans (hnd 9 (by decide)).symm
  exact ⟨h, prefixFiber_equiv_of_ndPrefixes_eq h⟩

/-- **Separation through the endpoint**: the bound for `row [1]` is `β = 0`, and `row [1]` is
not `0`-equivalent to the empty row, because the fiber at the label `[1]` would be `B0 1 ≅
Bstar0`. -/
theorem separation_regression :
    ¬ BFEquiv (L := lang ℕ Lp) 0 1 ![(Carrier.row (row1 1) : PrefixCarrier Bstar0 B0 Aall)]
      ![(Carrier.row row0 : PrefixCarrier Bstar0 B0 Aall)] := by
  intro h01
  obtain ⟨β, hβ, hprof⟩ :=
    exists_profile_bound (Lc := Lp) (Bstar := Bstar0) (B := B0) (A := Aall) 1
      sepBounded_regression upward_regression (row1 1)
  have hβ0 : β = 0 := Order.lt_one_iff.mp hβ
  subst hβ0
  obtain ⟨e⟩ := hprof row0 h01 ⟨[1], by decide⟩
  have e' : B0 1 ≃[Lp] Bstar0 := e
  exact (defaultLike_iff 1).mp ⟨e'⟩ |> fun h => absurd h (by decide)

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.FiberAssembly.exists_profile_bound,
   `FirstOrder.Language.FiberAssembly.prefixFiber_equiv_of_ndPrefixes_eq,
   `FirstOrder.Language.FiberAssembly.last_mem_of_prefix,
   `upward_regression, `sepBounded_regression, `not_bfEquiv_B0_one, `empty_row_regression,
   `default_tails_regression, `separation_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "fiber profile-bound regression guard: OK (empty row, different default tails with \
    isomorphic fibers, a genuine non-default component with a level-0 separation bound driving \
    the endpoint; headline declarations on standard axioms)"
