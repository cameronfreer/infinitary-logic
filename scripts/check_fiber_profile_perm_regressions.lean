/-
Regression guard for profile-preserving row permutations (`ModelTheory/FiberProfilePerm.lean`).

Generic lemma over `ℕ` with the equivalence "same parity": an **overlapping chain**
`0 ↦ 2, 2 ↦ 4` (not merely a swap) extends to a permutation preserving parity and fixing
everything outside `{0, 2, 4}`; a **compatible duplicate** matching `0 ↦ 2, 0 ↦ 2` is
accepted; the injective form applies to a swap.

Specialization: the profile-bound instance (one nullary relation, `B u` default-like iff
`5 ≤ u`, every letter allowed everywhere), where the one-letter rows `[7]`, `[9]`, `[11]` have
the same profile; the chain `[7] ↦ [9], [9] ↦ [11]` extends to a profile-preserving permutation
of all rows fixing `[13]`.  Headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_fiber_profile_perm_regressions.lean
-/
import InfinitaryLogic.ModelTheory.FiberProfilePerm

open Lean FirstOrder Language FiberAssembly

/-! ### Generic: same parity on `ℕ` -/

/-- Same parity. -/
def SameParity (a b : ℕ) : Prop := a % 2 = b % 2

instance (a b : ℕ) : Decidable (SameParity a b) := inferInstanceAs (Decidable (a % 2 = b % 2))

theorem sameParity_equivalence : Equivalence SameParity where
  refl _ := rfl
  symm h := h.symm
  trans h₁ h₂ := h₁.trans h₂

/-- **Overlapping chain** `0 ↦ 2, 2 ↦ 4`: a parity-preserving permutation realizing it and fixing
`6` and `1`. -/
theorem chain_regression :
    ∃ e : ℕ ≃ ℕ, e 0 = 2 ∧ e 2 = 4 ∧ (∀ x, SameParity x (e x)) ∧ e 6 = 6 ∧ e 1 = 1 := by
  obtain ⟨e, he, hE, hfix⟩ := exists_equiv_of_matching_injective sameParity_equivalence
    (r := ![0, 2]) (s := ![2, 4]) (by decide) (by decide) (by decide)
  refine ⟨e, he 0, he 1, hE, hfix 6 (by decide), hfix 1 (by decide)⟩

/-- **Compatible duplicates**: the matching `0 ↦ 2, 0 ↦ 2` is accepted. -/
theorem duplicate_regression : ∃ e : ℕ ≃ ℕ, e 0 = 2 ∧ ∀ x, SameParity x (e x) := by
  obtain ⟨e, he, hE, -⟩ := exists_equiv_of_matching sameParity_equivalence 2 ![0, 0] ![2, 2]
    (by decide) (by decide)
  exact ⟨e, he 0, hE⟩

/-! ### Specialization: rows with the same profile -/

inductive PSym : ℕ → Type
  | P : PSym 0

abbrev Lp : Language := ⟨fun _ => Empty, PSym⟩

def Bstar0 : Type := Unit

instance : Lp.Structure Bstar0 where
  funMap {_} g _ := (g : Empty).elim
  RelMap {_} _ _ := False

def B0 (_u : ℕ) : Type := Unit

instance (u : ℕ) : Lp.Structure (B0 u) where
  funMap {_} g _ := (g : Empty).elim
  RelMap {_} _ _ := u < 5

theorem relMap_Bstar0 {n : ℕ} (R : Lp.Relations n) (v : Fin n → Bstar0) :
    ¬ Structure.RelMap R v :=
  id

theorem relMap_B0 (u : ℕ) {n : ℕ} (R : Lp.Relations n) (v : Fin n → B0 u) :
    Structure.RelMap R v ↔ u < 5 :=
  Iff.rfl

/-- Components with `P` false are isomorphic to the default. -/
def toDefault (u : ℕ) (hu : 5 ≤ u) : B0 u ≃[Lp] Bstar0 where
  toEquiv := _root_.Equiv.refl Unit
  map_fun' := fun {_} g _ => (g : Empty).elim
  map_rel' := fun {_} R v =>
    ⟨fun h => (relMap_Bstar0 R _ h).elim,
      fun h => absurd hu (Nat.not_le.mpr ((relMap_B0 u R v).mp h))⟩

def Aall : ℕ → Set ℕ := fun _ => Set.univ

def row1 (u : ℕ) : Row Aall := ⟨[u], ⟨List.pairwise_singleton _ _, fun _ _ => Set.mem_univ _⟩⟩

/-- One-letter rows with default-like letters have no non-default prefixes. -/
theorem ndPrefixes_row1 (u : ℕ) (hu : 5 ≤ u) :
    ndPrefixes (DefaultLike Lp Bstar0 B0) (row1 u).1 = ∅ := by
  ext τ
  simp only [mem_ndPrefixes, Set.mem_empty_iff_false, iff_false, not_and, not_not]
  intro h
  have hlen : τ.1.length = 1 := le_antisymm h.length_le (List.length_pos_of_ne_nil τ.2)
  have hτ : τ.1 = [u] := h.eq_of_length hlen
  have hmem : τ.last ∈ τ.1 := List.getLast_mem _
  rw [hτ] at hmem
  rw [List.mem_singleton.mp hmem]
  exact ⟨toDefault u hu⟩

theorem sameProfile_row1 (u v : ℕ) (hu : 5 ≤ u) (hv : 5 ≤ v) :
    SameProfile Lp Bstar0 B0 Aall (row1 u) (row1 v) :=
  prefixFiber_equiv_of_ndPrefixes_eq ((ndPrefixes_row1 u hu).trans (ndPrefixes_row1 v hv).symm)

theorem row1_injective : Function.Injective row1 := fun u v h => by
  have := congrArg (fun p : Row Aall => p.1) h
  simpa [row1] using this

/-- **Row chain** `[7] ↦ [9], [9] ↦ [11]`: a profile-preserving permutation of all rows realizing
it and fixing `[13]`. -/
theorem row_chain_regression :
    ∃ e : Row Aall ≃ Row Aall, e (row1 7) = row1 9 ∧ e (row1 9) = row1 11 ∧
      (∀ t, SameProfile Lp Bstar0 B0 Aall t (e t)) ∧ e (row1 13) = row1 13 := by
  obtain ⟨e, he, hp, hfix⟩ := exists_profilePerm (Lc := Lp) (Bstar := Bstar0) (B := B0)
    ![row1 7, row1 9] ![row1 9, row1 11]
    (fun j j' => by
      fin_cases j <;> fin_cases j' <;>
        simp [row1_injective.eq_iff])
    (fun j => by
      fin_cases j
      · exact sameProfile_row1 7 9 (by decide) (by decide)
      · exact sameProfile_row1 9 11 (by decide) (by decide))
  refine ⟨e, he 0, he 1, hp, hfix _ fun j => ?_⟩
  fin_cases j <;> simp [row1_injective.eq_iff]

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.FiberAssembly.exists_equiv_of_matching,
   `FirstOrder.Language.FiberAssembly.exists_equiv_of_matching_injective,
   `FirstOrder.Language.FiberAssembly.sameProfile_equivalence,
   `FirstOrder.Language.FiberAssembly.exists_profilePerm,
   `chain_regression, `duplicate_regression, `sameProfile_row1, `row_chain_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "fiber profile-permutation regression guard: OK (overlapping chain with fixed outside \
    points, compatible duplicates, row chain with the same profile fixing an outside row; \
    headline declarations on standard axioms)"
