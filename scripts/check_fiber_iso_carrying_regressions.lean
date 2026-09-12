/-
Regression guard for fiber isomorphisms carrying a tuple (`ModelTheory/FiberIsoCarrying.lean`).

A single row `()`, labels over `ℕ`, the empty component language (relational), and the fiber at
a label `τ` being `Fin (2 * (τ.length - 1))`: the label `[0, 0]` has a two-point fiber and the
label `[0]` an **empty** fiber.  The tuple `a = (row, p, p)` **repeats** the point `p = 0` of the
two-point fiber; `b` is its image under the assembled automorphism reversing every fiber, so
`b = (row, 1, 1)` and `a ≡_β b` at every level.

Checked: the identity fiber isomorphisms `f₀` do **not** carry `a` to `b`, so a genuine
automorphism adjustment is needed; the theorem produces fiber isomorphisms carrying `a` to `b`,
with the cover constructed from `a` (`FiberCover.ofTuple`) and the orbit premise discharged on
the unoccupied fibers by the length-zero lemma; the adjusted isomorphisms agree with `f₀` on the
**unoccupied empty fiber** `[0]`; the cover counts (`pos_iff`) and the finiteness of occupied
fibers; and the empty tuple has orbit rank `0` in an **empty carrier**.  Headline declarations
use only the standard axioms.

Run with: lake env lean scripts/check_fiber_iso_carrying_regressions.lean
-/
import InfinitaryLogic.ModelTheory.FiberIsoCarrying
import Mathlib.Data.Fin.VecNotation

open Lean FirstOrder Language FiberAssembly

/-! ### The instance -/

/-- The fibers: `Fin (2 * (length τ - 1))`. -/
def Cf (_ : Unit) (τ : Label ℕ) : Type := Fin (2 * (τ.1.length - 1))

instance (r : Unit) (τ : Label ℕ) : Language.empty.Structure (Cf r τ) := Language.emptyStructure

instance (r : Unit) (τ : Label ℕ) : Countable (Cf r τ) := inferInstanceAs (Countable (Fin _))

/-- The two-point label. -/
def τ₀ : Label ℕ := ⟨[0, 0], by decide⟩

/-- The empty-fiber label. -/
def τ₁ : Label ℕ := ⟨[0], by decide⟩

theorem τ₀_ne_τ₁ : τ₀ ≠ τ₁ := fun h => by
  have := congrArg Subtype.val h
  simp [τ₀, τ₁] at this

/-- The point `0` of the two-point fiber. -/
def p0 : Cf () τ₀ := (⟨0, by decide⟩ : Fin (2 * (τ₀.1.length - 1)))

/-- The point `1` of the two-point fiber. -/
def p1 : Cf () τ₀ := (⟨1, by decide⟩ : Fin (2 * (τ₀.1.length - 1)))

theorem p0_ne_p1 : p0 ≠ p1 := fun h => by
  have := congrArg (fun x : Fin (2 * (τ₀.1.length - 1)) => x.val) h
  simp [p0, p1] at this

/-- The empty fiber is empty. -/
theorem empty_fiber_regression : IsEmpty (Cf () τ₁) :=
  ⟨fun x => by
    have := (show Fin (2 * (τ₁.1.length - 1)) from x).2
    simp [τ₁] at this⟩

abbrev M := Carrier Unit Cf

/-- Reversal of every fiber, as an isomorphism for the empty language. -/
def revIso (r : Unit) (τ : Label ℕ) : Cf r τ ≃[Language.empty] Cf (Equiv.refl Unit r) τ where
  toEquiv := (Fin.revPerm : Equiv.Perm (Fin (2 * (τ.1.length - 1))))
  map_fun' := fun {_} f _ => Empty.elim f
  map_rel' := fun {_} R _ => Empty.elim R

/-- The identity fiber isomorphisms. -/
def idIso (r : Unit) (τ : Label ℕ) : Cf r τ ≃[Language.empty] Cf (Equiv.refl Unit r) τ :=
  Language.Equiv.refl _ _

/-- The assembled reversal. -/
noncomputable def g : M ≃[lang ℕ Language.empty] M := assemble (Equiv.refl Unit) revIso

/-- The source tuple, with a **repeated** point. -/
def a : Fin 3 → M := ![Carrier.row (), Carrier.pt () τ₀ p0, Carrier.pt () τ₀ p0]

/-- The target tuple: the image of `a` under the reversal. -/
noncomputable def b : Fin 3 → M := ⇑g ∘ a

theorem b_one : b 1 = Carrier.pt () τ₀ p1 := by
  show Carrier.pt () τ₀ (Fin.rev (⟨0, _⟩ : Fin 2)) = Carrier.pt () τ₀ p1
  rfl

/-- **`f₀` does not carry `a` to `b`**: the identity isomorphisms leave `a` in place. -/
theorem identity_fails_regression : ⇑(assemble (Equiv.refl Unit) idIso) ∘ a ≠ b := by
  intro h
  have h1 := congrFun h 1
  rw [b_one] at h1
  have : Carrier.pt () τ₀ p0 = Carrier.pt () τ₀ p1 := h1
  exact p0_ne_p1 (Carrier.pt_inj_same this)

theorem owners_regression : ∀ i r τ, InFiber a r τ i → ∃ j, a j = Carrier.row r :=
  fun _ r _ _ => ⟨0, by cases r; rfl⟩

/-- Only the label `τ₀` carries a coordinate of `a`. -/
theorem inFiber_regression (r : Unit) (τ : Label ℕ) (i : Fin 3) (h : InFiber a r τ i) : τ = τ₀ := by
  obtain ⟨x, hx⟩ := h
  fin_cases i
  · exact absurd hx (by simp [a])
  · exact (Carrier.pt.inj hx).2.1.symm
  · exact (Carrier.pt.inj hx).2.1.symm

/-- The cover of `a`. -/
noncomputable def cov : FiberCover a := FiberCover.ofTuple a

/-- **Cover counts**: the two-point fiber is occupied, the empty fiber is not, and the occupied
fibers are finite. -/
theorem cover_regression :
    0 < cov.k () τ₀ ∧ ¬ 0 < cov.k () τ₁ ∧ {p : Unit × Label ℕ | 0 < cov.k p.1 p.2}.Finite :=
  ⟨(cov.pos_iff _ _).mpr ⟨1, p0, rfl⟩,
    fun h => τ₀_ne_τ₁ (inFiber_regression _ _ _ ((cov.pos_iff _ _).mp h).choose_spec).symm,
    cov.occupied_finite⟩

/-- **Carrying, with a genuine adjustment**: fiber isomorphisms carrying `a` to `b` exist and agree
with `f₀` on the unoccupied empty fiber. -/
theorem carrying_regression :
    ∃ f : ∀ r τ, Cf r τ ≃[Language.empty] Cf (Equiv.refl Unit r) τ,
      ⇑(assemble (Equiv.refl Unit) f) ∘ a = b ∧ f () τ₁ = idIso () τ₁ := by
  have hbf : ∀ β, BFEquiv (L := lang ℕ Language.empty) β 3 a b :=
    fun β => bfEquiv_all_of_automorphism g rfl β
  have horb : ∀ r τ, orbitRank (L := Language.empty) (cov.srcTuple r τ) ≤
      orbitRank (L := Language.empty) (cov.srcTuple () τ₀) := by
    intro r τ
    by_cases h : 0 < cov.k r τ
    · obtain ⟨i, hi⟩ := (cov.pos_iff r τ).mp h
      obtain rfl := inFiber_regression r τ i hi
      cases r
      exact le_rfl
    · rw [orbitRank_of_length_zero (Nat.eq_zero_of_not_pos h)]
      exact _root_.zero_le
  obtain ⟨f, hf, hf₀⟩ := exists_fiber_isos_carrying (orbitRank (L := Language.empty)
    (cov.srcTuple () τ₀)) (Equiv.refl Unit) idIso (matched_assemble _ revIso a)
    owners_regression (hbf _) cov horb
  exact ⟨f, hf, hf₀ () τ₁ cover_regression.2.1⟩

instance : Language.empty.Structure Empty := Language.emptyStructure

/-- **Empty tuple in an empty carrier**: orbit rank `0`. -/
theorem empty_carrier_regression :
    orbitRank (L := Language.empty) (Fin.elim0 : Fin 0 → Empty) = 0 :=
  orbitRank_elim0

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.FiberAssembly.exists_fiber_isos_carrying,
   `FirstOrder.Language.FiberAssembly.matched_assemble,
   `FirstOrder.Language.FiberAssembly.FiberCover.ofTuple,
   `FirstOrder.Language.FiberAssembly.FiberCover.pos_iff,
   `FirstOrder.Language.FiberAssembly.FiberCover.occupied_finite,
   `FirstOrder.Language.orbitRank_elim0, `FirstOrder.Language.orbitRank_of_length_zero,
   `identity_fails_regression, `cover_regression, `carrying_regression,
   `empty_fiber_regression, `empty_carrier_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "fiber iso-carrying regression guard: OK (identity isomorphisms fail to carry, genuine \
    adjustment with a repeated coordinate, unoccupied empty fiber kept, cover counts and finite \
    occupied set, empty tuple in an empty carrier; headline declarations on standard axioms)"
