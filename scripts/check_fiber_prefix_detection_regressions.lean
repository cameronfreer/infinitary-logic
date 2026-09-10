/-
Regression guard for finite-prefix detection (`ModelTheory/FiberPrefixDetection.lean`).

Over `U = ℕ` with the upward-closed predicate `D u := 5 ≤ u` ("default-like letters are those
`≥ 5`").  Checked: the **empty reference row** (`r = []`, `s = [1]`: a distinguishing prefix of
length `1 = 0 + 1`); **different default tails with identical profiles** (`[1, 2, 7]` and
`[1, 2, 9]` have the same non-default prefix sets, so no distinguishing prefix is claimed);
and a distinguishing prefix **first appearing at length `r.length + 1`** (`r = [1]`,
`s = [1, 2, 3]`, where `[1, 2]` of length `2` distinguishes although `s` also has the longer
non-default prefix `[1, 2, 3]`).  Headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_fiber_prefix_detection_regressions.lean
-/
import InfinitaryLogic.ModelTheory.FiberPrefixDetection

open Lean FirstOrder Language FiberAssembly

/-- Default-like letters: those `≥ 5`. -/
def D5 : ℕ → Prop := fun u => 5 ≤ u

instance : DecidablePred D5 := fun u => inferInstanceAs (Decidable (5 ≤ u))

theorem upward_regression : UpwardClosed D5 := fun huv hu => le_trans hu huv

/-- The label `[1]`. -/
def l1 : Label ℕ := ⟨[1], by decide⟩

/-- **Empty reference row**: `[1]` is a non-default prefix of `[1]` and of nothing in `[]`. -/
theorem empty_row_regression :
    l1 ∈ ndPrefixes D5 [1] ∧ l1 ∉ ndPrefixes D5 [] ∧
    ∃ τ : Label ℕ, τ.1.length ≤ ([] : List ℕ).length + 1 ∧ ¬ D5 τ.last ∧
      ¬ (τ.1 <+: [] ↔ τ.1 <+: [1]) := by
  refine ⟨⟨List.prefix_refl _, by decide⟩, ?_, ?_⟩
  · rintro ⟨h, -⟩
    have := h.length_le
    simp [l1] at this
  · exact exists_short_distinguishing_prefix upward_regression (by decide) (fun h => by
      have : l1 ∈ ndPrefixes D5 [1] := ⟨List.prefix_refl _, by decide⟩
      rw [← h] at this
      have := this.1.length_le
      simp [l1] at this)

/-- The non-default prefixes of a word over `ℕ` with `D5`, as a decidable membership test on
labels of bounded length. -/
theorem nd_mem_iff (r : List ℕ) (τ : Label ℕ) :
    τ ∈ ndPrefixes D5 r ↔ τ.1 <+: r ∧ ¬ 5 ≤ τ.last := Iff.rfl

/-- **Different default tails, identical profiles**: `[1, 2, 7]` and `[1, 2, 9]` have the same
non-default prefixes (`[1]` and `[1, 2]`; the full words end in default-like letters). -/
theorem same_profile_regression : ndPrefixes D5 [1, 2, 7] = ndPrefixes D5 [1, 2, 9] := by
  ext τ
  simp only [nd_mem_iff]
  constructor
  · rintro ⟨hp, hd⟩
    rcases List.prefix_concat_iff.mp (show τ.1 <+: [1, 2] ++ [7] from hp) with h | hp'
    · exact absurd (show 5 ≤ τ.last by unfold Label.last; simp [h]) hd
    · exact ⟨hp'.trans (List.prefix_append _ _), hd⟩
  · rintro ⟨hp, hd⟩
    rcases List.prefix_concat_iff.mp (show τ.1 <+: [1, 2] ++ [9] from hp) with h | hp'
    · exact absurd (show 5 ≤ τ.last by unfold Label.last; simp [h]) hd
    · exact ⟨hp'.trans (List.prefix_append _ _), hd⟩

/-- The label `[1, 2]`. -/
def l12 : Label ℕ := ⟨[1, 2], by decide⟩

/-- The label `[1, 2, 3]`. -/
def l123 : Label ℕ := ⟨[1, 2, 3], by decide⟩

/-- **A distinguishing prefix first appearing at length `r.length + 1`**: with `r = [1]` and
`s = [1, 2, 3]`, the theorem yields a distinguishing non-default label of length at most `2`,
and `[1, 2]` is such a label, although the longer `[1, 2, 3]` is also a non-default prefix of
`s`. -/
theorem extra_position_regression :
    (∃ τ : Label ℕ, τ.1.length ≤ [1].length + 1 ∧ ¬ D5 τ.last ∧
      ¬ (τ.1 <+: [1] ↔ τ.1 <+: [1, 2, 3])) ∧
    (l12.1.length = [1].length + 1 ∧ ¬ D5 l12.last ∧ ¬ (l12.1 <+: [1] ↔ l12.1 <+: [1, 2, 3])) ∧
    l123 ∈ ndPrefixes D5 [1, 2, 3] := by
  refine ⟨exists_short_distinguishing_prefix upward_regression (by decide) (fun h => ?_),
    ⟨rfl, by decide, fun h => ?_⟩, ⟨List.prefix_refl _, by decide⟩⟩
  · have : l12 ∈ ndPrefixes D5 [1, 2, 3] := ⟨⟨[3], rfl⟩, by decide⟩
    rw [← h] at this
    have := this.1.length_le
    simp [l12] at this
  · have := (h.mpr ⟨[3], rfl⟩).length_le
    simp [l12] at this

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.FiberAssembly.exists_short_distinguishing_prefix,
   `FirstOrder.Language.FiberAssembly.last_le_last_of_prefix,
   `upward_regression, `empty_row_regression, `same_profile_regression,
   `extra_position_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "fiber prefix-detection regression guard: OK (empty reference row, identical profiles \
    with different default tails, distinguishing prefix at length r.length + 1; headline \
    declarations on standard axioms)"
