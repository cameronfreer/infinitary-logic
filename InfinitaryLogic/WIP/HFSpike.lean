/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Theory
import InfinitaryLogic.Lomega1omega.Operations
import Mathlib.ModelTheory.Satisfiability

/-!
# HF spike: the finitary fragment and its compactness (issue #18, stop/go gate)

**Deliberately independent of `AdmissibleFragmentCore` and `FiniteCompactFragment`.**  An honest HF
fragment *cannot* satisfy those interfaces:

* `AdmissibleFragmentCore` demands closure under **every external ℕ-indexed** `iInf`/`iSup`, but the
  image of first-order syntax is closed only under **finite** conjunctions and disjunctions;
* `FiniteCompactFragment.height_gt_omega` excludes the genuine HF height `ω`.

So this file defines the fragment as a plain set and proves compactness for it directly.  The
decisive acceptance condition is that the proof invokes **Mathlib's first-order compactness**, not a
stored `compact` field.

## Architectural finding for #18

The replacement fragment interface must express closure under **internally permitted / coded**
families — for HF, the *finite* ones — rather than arbitrary external ℕ-families.  Until that
interface exists, `AdmissibleFragmentCore.hf := Set.univ` should stay labelled a legacy placeholder
rather than be mutated into something its fields cannot honestly support.
-/

namespace FirstOrder.Language

variable {L : Language.{0, 0}}

/-- **The finitary fragment**: the image of first-order syntax in `Lω₁ω`.  This is `L_HF = L_ωω`. -/
def finitaryFragment (L : Language.{0, 0}) : Set L.Sentenceω :=
  Set.range Sentence.toLω

theorem mem_finitaryFragment_iff {φ : L.Sentenceω} :
    φ ∈ finitaryFragment L ↔ ∃ φ₀ : L.Sentence, φ₀.toLω = φ := Iff.rfl

/-- The **full preimage theory** — every first-order sentence whose image lies in `T`, not one
chosen representative per member.  Choosing representatives would need `Classical.choice` and would
make the model correspondence direction-sensitive. -/
def foTheory (T : Set L.Sentenceω) : L.Theory :=
  {φ₀ : L.Sentence | φ₀.toLω ∈ T}

/-- **Model correspondence.**  For a theory inside the finitary fragment, models of the preimage
theory are exactly models of the original. -/
theorem model_foTheory_iff {T : Set L.Sentenceω} (hT : T ⊆ finitaryFragment L)
    (M : Type) [L.Structure M] [Nonempty M] :
    M ⊨ foTheory T ↔ Theoryω.Model T M := by
  constructor
  · intro hM φ hφ
    obtain ⟨φ₀, rfl⟩ := hT hφ
    exact (Sentence.realize_toLω φ₀).mpr (hM.realize_of_mem φ₀ hφ)
  · intro hM
    refine ⟨fun {φ₀} hφ₀ => ?_⟩
    exact (Sentence.realize_toLω φ₀).mp (hM _ hφ₀)

/-- **Compactness for the finitary fragment**, derived from Mathlib's first-order compactness.

No `compact` field is consulted: the infinitary finite-satisfiability hypothesis is pushed through
`toLω` to the preimage theory, Mathlib supplies a model, and the correspondence carries it back. -/
theorem finitaryFragment_compact {T : Set L.Sentenceω} (hT : T ⊆ finitaryFragment L)
    (hfin : ∀ F ⊆ T, F.Finite → ∃ (M : Type) (_ : L.Structure M) (_ : Nonempty M),
      Theoryω.Model F M) :
    ∃ (M : Type) (_ : L.Structure M) (_ : Nonempty M), Theoryω.Model T M := by
  -- every finite subset of the preimage theory is satisfiable
  have hfs : (foTheory T).IsFinitelySatisfiable := by
    intro F₀ hF₀
    obtain ⟨M, instM, neM, hM⟩ :=
      hfin (Sentence.toLω '' (F₀ : Set L.Sentence))
        (by rintro _ ⟨φ₀, hφ₀, rfl⟩; exact hF₀ hφ₀)
        (F₀.finite_toSet.image _)
    letI : L.Structure M := instM
    haveI := neM
    haveI : M ⊨ (↑F₀ : L.Theory) :=
      ⟨fun {φ₀} hφ₀ => (Sentence.realize_toLω φ₀).mp (hM _ ⟨φ₀, hφ₀, rfl⟩)⟩
    exact Theory.Model.isSatisfiable M
  -- Mathlib first-order compactness
  obtain ⟨M⟩ := Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr hfs
  exact ⟨M, inferInstance, inferInstance, (model_foTheory_iff hT M).mp M.is_model⟩

end FirstOrder.Language
