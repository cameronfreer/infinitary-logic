/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.Fragment.Honest
import InfinitaryLogic.Lomega1omega.Theory
import InfinitaryLogic.Lomega1omega.FirstOrderImage
import Mathlib.ModelTheory.Satisfiability
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# The HF fragment (issue #18)

`L_HF = L_ωω`: the first-order image inside `Lω₁ω`, as an honest admissible fragment, plus its
compactness theorem derived from Mathlib.

**This is the regression oracle for the interface.**  Any proposed change to `AdmissibleFragment`
must keep all four conditions:

1. the underlying formulas are exactly the `toLω`-image (`sentence_slice_hfFragment`);
2. coded families reduce to finite ones — here, to none at all;
3. the compactness theorem is `finitaryFragment_compact`;
4. no adapter widens it back to all of `Lω₁ω`.

**Where the emptiness lives.**  `hfFamily.IsFamilyCode` is `False`.  Not the index type's
cardinality, and not `einf`'s `⊤`-padding, which is legitimate for a real infinitary code.  The
forbidden move is granting the certificate to a finite code and using padding to manufacture a
primitive `iInf`.

**Universes.**  The syntax layer is `Language.{u, v}`.  Only `finitaryFragment_compact` is
specialized to `{0, 0}`, and that restriction belongs to Mathlib's compactness theorem — a semantic
limitation must not propagate back onto a syntactic definition.

**Not built on the legacy structures.**  `AdmissibleFragmentCore.hf := Set.univ` is a quarantined
placeholder; nothing here uses it, and nothing here may be proved from it.
-/

namespace FirstOrder.Language

universe u v uCode uIndex

variable {L : Language.{0, 0}}

/-- The all-arity first-order image: every formula containing no infinitary node. -/
def hfSet (L : Language.{u, v}) : Set (Σ n, L.BoundedFormulaω Empty n) :=
  {p | p.2.IsFirstOrder}

@[simp] theorem mem_hfSet_iff {n : ℕ} {φ : L.BoundedFormulaω Empty n} :
    (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ hfSet L ↔ φ.IsFirstOrder := Iff.rfl

/-- **The HF fragment.**  Each field is now one appeal to the first-order-image API: three
structural equations and the two negative facts.  Compare the five hand-rolled constructor
inversions this replaces. -/
def hfFragment (L : Language.{u, v}) : Fragment L where
  toSet := hfSet L
  imp_left_mem h := (BoundedFormulaω.isFirstOrder_imp_iff.mp h).1
  imp_right_mem h := (BoundedFormulaω.isFirstOrder_imp_iff.mp h).2
  all_mem h := BoundedFormulaω.isFirstOrder_all_iff.mp h
  iInf_mem h := absurd h (BoundedFormulaω.not_isFirstOrder_iInf _)
  iSup_mem h := absurd h (BoundedFormulaω.not_isFirstOrder_iSup _)


/-- **The finitary fragment**: the image of first-order syntax in `Lω₁ω`.  This is `L_HF = L_ωω`. -/
def finitaryFragment (L : Language.{u, v}) : Set L.Sentenceω :=
  Set.range Sentence.toLω

theorem mem_finitaryFragment_iff {L : Language.{u, v}} {φ : L.Sentenceω} :
    φ ∈ finitaryFragment L ↔ ∃ φ₀ : L.Sentence, φ₀.toLω = φ := Iff.rfl

/-- **The oracle, condition 1.**  The sentence slice of `hfFragment` is exactly `finitaryFragment`.
Any proposed `AdmissibleFragment` whose HF instance fails this is wrong.

Both sides are now universe-general; only `finitaryFragment_compact` below stays at `{0, 0}`, and
that restriction belongs to Mathlib's compactness theorem, not to the syntax. -/
theorem sentence_slice_hfFragment (L : Language.{u, v}) :
    {φ : L.Sentenceω | (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ hfFragment L} =
      finitaryFragment L := by
  ext φ
  simp only [Set.mem_ofPred_eq, Fragment.mem_def, mem_finitaryFragment_iff]
  exact Iff.rfl

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
theorem finitaryFragment_compact {T : L.Theoryω} (hT : T ⊆ finitaryFragment L)
    (hfin : T.IsFinitelySatisfiable) : T.IsSatisfiable := by
  -- every finite subset of the preimage theory is satisfiable
  have hfs : (foTheory T).IsFinitelySatisfiable := by
    intro F₀ hF₀
    obtain ⟨M, instM, neM, hM⟩ :=
      hfin (Sentence.toLω '' (F₀ : Set L.Sentence))
        (by rintro _ ⟨φ₀, hφ₀, rfl⟩; exact hF₀ hφ₀)
        (F₀.finite_toSet.image _)
    let : L.Structure M := instM
    have := neM
    have : M ⊨ (↑F₀ : L.Theory) :=
      ⟨fun {φ₀} hφ₀ => (Sentence.realize_toLω φ₀).mp (hM _ ⟨φ₀, hφ₀, rfl⟩)⟩
    exact Theory.Model.isSatisfiable M
  -- Mathlib first-order compactness
  obtain ⟨M⟩ := Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr hfs
  exact ⟨M, inferInstance, inferInstance, (model_foTheory_iff hT M).mp M.is_model⟩


/-! ## Gate 4 — the HF oracle

For HF the certificate is empty, so `CodedFamily` is uninhabited and the upward-closure fields of
any `AdmissibleFragment` over it are vacuous.  Note where the emptiness lives: in `IsFamilyCode`,
**not** in the index type's cardinality and **not** in `einf`'s padding. -/

/-- **Gate 4.**  `CodedFamily` over HF is uninhabited.

Stated over `hfFamily`, the family-layer HF presentation, so the syntax consumers of HF depend on
no presentation carrying theory decoding or `Sigma1`.  The emptiness comes solely from
`IsFamilyCode := False`. -/
theorem isEmpty_codedFamily_hf : IsEmpty (CodedFamily (hfFamily L) n) :=
  isEmpty_codedFamily_hfFamily

/-- Consequently every upward-closure obligation over HF is vacuous, for **any** target set. -/
theorem hf_coded_closure_vacuous (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    ∀ F : CodedFamily (hfFamily L) n,
      (∀ i, (⟨n, F.decode i⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ S) →
        (⟨n, codedIInf F⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ S :=
  hfFamily_coded_closure_vacuous S


/-! ## Step 4 — the honest HF instance

Essentially a structure literal: the base is `hfFragment`, and both upward fields are closed by
certificate absurdity.  That it *is* nearly definitional is the signal that the signature is right. -/

/-- **The HF admissible fragment.**  No adapter, no widening. -/
def hfAdmissibleFragment (L : Language.{0, 0}) : AdmissibleFragment (hfFamily L) where
  toFragment := hfFragment L
  iInf_coded_mem := fun F _ => absurd F.infinitary not_false
  iSup_coded_mem := fun F _ => absurd F.infinitary not_false

/-- **Oracle condition 1, at the interface level.**  The HF admissible fragment's underlying
`Fragment` is exactly `hfFragment`, whose sentence slice is `finitaryFragment`. -/
theorem hfAdmissibleFragment_toFragment (L : Language.{0, 0}) :
    (hfAdmissibleFragment L).toFragment = hfFragment L := rfl


/-! ## Universe gate — CLOSED

The structures are **language-indexed and universe-polymorphic**: `FamilyPresentation L` for
`L : Language.{u, v}`, so `FamilyPresentation L[[J]]` is well-formed for an arbitrary parameter
type `J`.  This is the generalization route, chosen over restricting the EM adapter to `J : Type 0`
— that restriction would silently weaken the existing arbitrary-target-order EM surface and confuse
a universe limitation with the later mathematical question of which template theories are genuinely
coded.

It does **not** claim a presentation for `L` lifts to one for `L[[J]]`; whether such a lift exists is
genuine #19A coding content.  Only the *signature* is settled here.

**Diagnosis of an earlier false alarm.**  A probe written with the result annotation `: Type` was
reported as a universe-plumbing blocker.  It was a bug in the probe, not the API: bare `Type` means
`Type 0`, and that result constraint propagates *backward*, forcing Lean to expect
`FamilyPresentation.{0,0,0,0}` and producing a misleading error on the presentation argument.
Explicit `.{…}` arguments cannot fix it, because the `Type 0` result constraint remains.  Writing
`Type _` (or `Sort _`) lets the presentation universes be inferred and both probes compile. -/

section UniverseGate

/-- Arbitrary parameter type, arbitrary language universes: a coded family elaborates. -/
example (Lb : Language.{u, v}) (J : Type w) (B : FamilyPresentation Lb[[J]]) (m : ℕ) : Type _ :=
  CodedFamily B m

/-- …and so does the fragment wrapper. -/
example (Lb : Language.{u, v}) (J : Type w) (B : FamilyPresentation Lb[[J]]) : Type _ :=
  AdmissibleFragment B

end UniverseGate

end FirstOrder.Language
