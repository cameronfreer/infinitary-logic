/-
Regression guard for the Cantor-indexed family (`ModelTheory/FiberCantorFamily.lean`).

Checked: `cantorPath` on the constant-`false` sequence equals `n / 2` at every position and on
the constant-`true` sequence gives `0, 1, 1, 2, 2, 3`; **injectivity** at two sequences differing
at `0`; **allowedness**; the **approximation threshold** at level `2` with `N = 4` as the
**universal tail condition** (every `k ≥ 4`, not only `k = 4`), with instances at `k = 4` and
`k = 7`; and the **package** applied to the two constant sequences, extracting and using every
conjunct: the base's rank, countability of both companions, equivalence of both to the base at
level `3`, non-isomorphism of both with the base, and pairwise non-isomorphism in both
directions.  Headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_fiber_cantor_family_regressions.lean
-/
import InfinitaryLogic.ModelTheory.FiberCantorFamily

open Lean FirstOrder Language FiberAssembly ExactOmega

/-- The constant-`false` sequence. -/
def zF : ℕ → Bool := fun _ => false

/-- The constant-`true` sequence. -/
def zT : ℕ → Bool := fun _ => true

/-- **Values**: `π_{false}` is `n / 2` everywhere; `π_{true}` is `0, 1, 1, 2, 2, 3`. -/
theorem values_regression :
    (∀ k, cantorPath zF k = k / 2) ∧
    cantorPath zT 0 = 0 ∧ cantorPath zT 1 = 1 ∧ cantorPath zT 2 = 1 ∧
    cantorPath zT 3 = 2 ∧ cantorPath zT 4 = 2 ∧ cantorPath zT 5 = 3 :=
  ⟨fun k => by simp [cantorPath, zF], rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem zF_ne_zT : zF ≠ zT := fun h => absurd (congrFun h 0) (by decide)

/-- **Injectivity** at sequences differing at `0`: the paths differ at position `1`. -/
theorem injective_regression :
    cantorPath zF ≠ cantorPath zT ∧ cantorPath zF 1 ≠ cantorPath zT 1 :=
  ⟨cantorPath_injective.ne zF_ne_zT, by decide⟩

/-- **Allowedness** of both paths. -/
theorem allowed_regression :
    IsAllowedPath Aiic (cantorPath zF) ∧ IsAllowedPath Aiic (cantorPath zT) :=
  ⟨cantorPath_allowed zF, cantorPath_allowed zT⟩

/-- **Approximation at level `2` with threshold `4`**, as the universal tail condition, and two
instances of it. -/
theorem threshold_regression :
    (∀ k, 4 ≤ k → BFEquiv (L := Language.empty) ((2 : ℕ) : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → ℕ) (Fin.elim0 : Fin 0 → Bfin (cantorPath zT k))) ∧
    BFEquiv (L := Language.empty) ((2 : ℕ) : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → ℕ) (Fin.elim0 : Fin 0 → Bfin (cantorPath zT 4)) ∧
    BFEquiv (L := Language.empty) ((2 : ℕ) : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → ℕ) (Fin.elim0 : Fin 0 → Bfin (cantorPath zT 7)) :=
  ⟨cantorPath_pathApproxAt zT 2, cantorPath_pathApproxAt zT 2 4 le_rfl,
    cantorPath_pathApproxAt zT 2 7 (by decide)⟩

/-- **The package**, every conjunct extracted and used on the two constant sequences. -/
theorem package_regression :
    internalScottRank (L := lang ℕ Language.empty) Carrier' = Ordinal.omega0.{0} ∧
    Countable (CantorCompanion zF) ∧ Countable (CantorCompanion zT) ∧
    BFEquiv (L := lang ℕ Language.empty) ((3 : ℕ) : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → CantorCompanion zF) (Fin.elim0 : Fin 0 → Carrier') ∧
    BFEquiv (L := lang ℕ Language.empty) ((3 : ℕ) : Ordinal.{0}) 0
      (Fin.elim0 : Fin 0 → CantorCompanion zT) (Fin.elim0 : Fin 0 → Carrier') ∧
    IsEmpty (CantorCompanion zF ≃[lang ℕ Language.empty] Carrier') ∧
    IsEmpty (CantorCompanion zT ≃[lang ℕ Language.empty] Carrier') ∧
    IsEmpty (CantorCompanion zF ≃[lang ℕ Language.empty] CantorCompanion zT) ∧
    IsEmpty (CantorCompanion zT ≃[lang ℕ Language.empty] CantorCompanion zF) := by
  obtain ⟨hrank, hcount, hequiv, hbase, hpair⟩ := cantorFamily
  exact ⟨hrank, hcount zF, hcount zT, hequiv zF _ (Ordinal.natCast_lt_omega0 3),
    hequiv zT _ (Ordinal.natCast_lt_omega0 3), hbase zF, hbase zT, hpair zF zT zF_ne_zT,
    hpair zT zF zF_ne_zT.symm⟩

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.FiberAssembly.ExactOmega.cantorPath_injective,
   `FirstOrder.Language.FiberAssembly.ExactOmega.cantorPath_allowed,
   `FirstOrder.Language.FiberAssembly.ExactOmega.cantorPath_pathApproxAt,
   `FirstOrder.Language.FiberAssembly.ExactOmega.cantorCompanion_bfEquiv,
   `FirstOrder.Language.FiberAssembly.ExactOmega.cantorCompanion_not_iso,
   `FirstOrder.Language.FiberAssembly.ExactOmega.cantorCompanions_not_iso,
   `FirstOrder.Language.FiberAssembly.ExactOmega.cantorFamily,
   `values_regression, `injective_regression, `allowed_regression, `threshold_regression,
   `package_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "fiber Cantor-family regression guard: OK (path values, injectivity, allowedness, \
    universal-tail threshold at level 2 with N = 4, and every package conjunct used on two \
    constant sequences; headline declarations on standard axioms)"
