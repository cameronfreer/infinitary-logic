/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.WIP.HFSpike
import InfinitaryLogic.Lomega1omega.Fragment

/-!
# The HF fragment as an ordinary `Fragment` (issue #18, step 1)

Architecture-independent: this file mentions no admissible-set interface at all.  It builds the
all-arity `toLω`-image as a `Fragment` and proves its sentence slice is exactly the spike's
`finitaryFragment`.

That makes the downward-closure argument **executable** rather than asserted, and gives every later
interface proposal a compiler-enforced oracle: whatever `AdmissibleFragment` turns out to be, its HF
instance must have *this* underlying `Fragment`.

## The load-bearing observation

Every closure field of `Fragment` is **downward** — "a component of a member is a member" — never
upward.  So the infinitary fields hold **vacuously** here: `toLω` emits no `iInf`/`iSup`
constructor, so no member is one.

By contrast `AdmissibleFragmentCore.closed_iInf` is *upward* over arbitrary external ℕ-families, and
HF cannot satisfy it: a constant family of members has a genuine `iInf` node as its conjunction, and
that node is outside the image.  Unsatisfiable, not merely inconvenient.
-/

namespace FirstOrder.Language

variable {L : Language.{0, 0}}

/-- The all-arity `toLω`-image. -/
def hfSet (L : Language.{0, 0}) : Set (Σ n, L.BoundedFormulaω Empty n) :=
  Set.range fun p : Σ n, L.BoundedFormula Empty n => ⟨p.1, p.2.toLω⟩

theorem mem_hfSet_iff {n : ℕ} {φ : L.BoundedFormulaω Empty n} :
    (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ hfSet L ↔
      ∃ φ₀ : L.BoundedFormula Empty n, φ₀.toLω = φ := by
  constructor
  · rintro ⟨⟨m, φ₀⟩, hp⟩
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp hp
    exact ⟨φ₀, eq_of_heq h⟩
  · rintro ⟨φ₀, rfl⟩
    exact ⟨⟨n, φ₀⟩, rfl⟩

/-- **The HF fragment.**  All five closure fields are discharged by inverting `toLω` on the
constructor: three structurally, two vacuously. -/
def hfFragment (L : Language.{0, 0}) : Fragment L where
  toSet := hfSet L
  imp_left_mem := by
    rintro n φ ψ h
    obtain ⟨φ₀, hφ₀⟩ := mem_hfSet_iff.mp h
    cases φ₀ with
    | imp a b => exact mem_hfSet_iff.mpr ⟨a, by injection hφ₀⟩
    | falsum => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
    | equal => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
    | rel => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
    | all => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
  imp_right_mem := by
    rintro n φ ψ h
    obtain ⟨φ₀, hφ₀⟩ := mem_hfSet_iff.mp h
    cases φ₀ with
    | imp a b => exact mem_hfSet_iff.mpr ⟨b, by injection hφ₀⟩
    | falsum => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
    | equal => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
    | rel => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
    | all => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
  all_mem := by
    rintro n φ h
    obtain ⟨φ₀, hφ₀⟩ := mem_hfSet_iff.mp h
    cases φ₀ with
    | all a => exact mem_hfSet_iff.mpr ⟨a, by injection hφ₀⟩
    | falsum => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
    | equal => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
    | rel => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
    | imp => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
  -- vacuous: `toLω` emits no infinitary constructor
  iInf_mem := by
    rintro n φs h
    obtain ⟨φ₀, hφ₀⟩ := mem_hfSet_iff.mp h
    cases φ₀ <;> exact absurd hφ₀ (by simp [BoundedFormula.toLω])
  iSup_mem := by
    rintro n φs h
    obtain ⟨φ₀, hφ₀⟩ := mem_hfSet_iff.mp h
    cases φ₀ <;> exact absurd hφ₀ (by simp [BoundedFormula.toLω])

/-- **The oracle, condition 1.**  The sentence slice of `hfFragment` is exactly the spike's
`finitaryFragment`.  Any proposed `AdmissibleFragment` whose HF instance fails this is wrong. -/
theorem sentence_slice_hfFragment :
    {φ : L.Sentenceω | (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ hfFragment L} =
      finitaryFragment L := by
  ext φ
  simp only [Set.mem_setOf_eq, Fragment.mem_def, mem_finitaryFragment_iff]
  exact mem_hfSet_iff

end FirstOrder.Language
