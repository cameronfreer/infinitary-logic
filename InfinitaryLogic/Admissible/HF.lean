/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.Fragment.Honest
import InfinitaryLogic.Admissible.Predicates
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

**Where the emptiness lives.**  `hfPresentation.CodesInfFamily` is `False`.  Not the index type's
cardinality — `Index := Fin k` is genuinely finite with a perfectly good `Encodable` — and not
`einf`'s `⊤`-padding, which is legitimate for a real infinitary code.  The forbidden move is
granting the certificate to a finite code and using padding to manufacture a primitive `iInf`.

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
  simp only [Set.mem_setOf_eq, Fragment.mem_def, mem_finitaryFragment_iff]
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


/-! ## Gate 4 — the HF oracle

For HF the certificate is empty, so `CodedFamily` is uninhabited and the upward-closure fields of
any `AdmissibleFragment` over it are vacuous.  Note where the emptiness lives: in
`CodesInfFamily`, **not** in the index type's cardinality and **not** in `einf`'s padding. -/

/-- The HF presentation: codes are (say) natural numbers naming finite index types, and **no code
names an infinitary family**. -/
def hfPresentation (L : Language.{u, v}) : AdmissiblePresentation L where
  -- a code carries its enumeration, not merely a cardinality: `k` alone would decode every theory
  -- of size `≤ k`, so a code would name many theories and `decodes_theory_unique` would fail
  Code := Σ k : ℕ, Fin k → L.Sentenceω
  Index := fun c => Fin c.1
  indexEncodable := fun _ => inferInstance
  CodesInfFamily := fun _ => False
  DecodesFamily := fun _ _ _ => True
  -- vacuous: no code is infinitary
  decodes_unique := fun h _ _ => absurd h not_false
  -- the code *is* the enumeration; the theory it names is that enumeration's range
  DecodesTheory := fun c T => Set.range c.2 = T
  decodes_theory_unique := fun h h' => h ▸ h'
  -- first-order compactness carries no definability restriction, so nothing is excluded here
  Sigma1 := fun _ => True

/-- **Oracle condition 3, the hypothesis side.**  `A`-finiteness over HF **is** ordinary
finiteness.  This is what makes HF's compactness theorem `finitaryFragment_compact` by
specialization — hypothesis for hypothesis — rather than through a bridging lemma. -/
theorem hf_aFinite_iff {L : Language.{u, v}} {T : Set L.Sentenceω} :
    AFinite (hfPresentation L) T ↔ T.Finite := by
  constructor
  · rintro ⟨⟨k, f⟩, rfl⟩
    exact Set.finite_range f
  · intro hT
    obtain ⟨s, rfl⟩ := hT.exists_finset_coe
    haveI : Fintype {x // x ∈ s} := FinsetCoe.fintype s
    refine ⟨⟨Fintype.card {x // x ∈ s},
      fun i => ((Fintype.equivFin {x // x ∈ s}).symm i : L.Sentenceω)⟩, ?_⟩
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ((Fintype.equivFin {x // x ∈ s}).symm i).2
    · intro hx
      exact ⟨Fintype.equivFin _ ⟨x, hx⟩, by simp⟩

/-- **The definability side is deliberately enlarged, and this is NOT Σ₁-on-HF.**

Σ₁-definability over HF is ordinary computable enumerability (Keisler–Knight §2.2), so the honest
`Sigma1` for HF is the c.e. predicate, not `True`.  `hfPresentation` sets it to `True`, which
*widens* the domain of the compactness statement to every theory.  That widening is sound — it is
how unrestricted first-order compactness is recovered — but it must not be read as a claim that
every theory is `A`-c.e.

Stated as an equation about the presentation rather than as a theorem named `hf_acEnumerable`,
precisely so that no consumer can cite a mathematically specific name for it.  Nothing downstream
may depend on this: `hf_compact_of_aFinite` below is the unconditional theorem, and `hf_compactFor`
discards the hypothesis rather than using it.  #19A replaces the `Sigma1` field with decoding data
(`DefinesSigmaTheory`), at which point HF's instantiation must become the c.e. predicate and this
equation must fail to typecheck. -/
theorem hfPresentation_sigma1_eq_top (L : Language.{u, v}) :
    (hfPresentation L).Sigma1 = fun _ => True := rfl

/-- **HF compactness in the external `A`-finite form, with NO definability hypothesis.**

This is the theorem the EM adapters and every other consumer should use.  It is strictly stronger
than `hf_compactFor`, and stating it separately is what keeps the enlarged `Sigma1` from becoming
load-bearing: a consumer that needs compactness gets it here without ever mentioning
`ACEnumerable`, so tightening HF's `Sigma1` to the honest c.e. predicate in #19A cannot break it.

The only translation is `hf_aFinite_iff`; the mathematics is `finitaryFragment_compact`. -/
theorem hf_compact_of_aFinite {T : Set L.Sentenceω} (hT : T ⊆ finitaryFragment L)
    (hfin : ∀ T₀ ⊆ T, AFinite (hfPresentation L) T₀ →
      ∃ (M : Type) (_ : L.Structure M) (_ : Nonempty M), Theoryω.Model T₀ M) :
    ∃ (M : Type) (_ : L.Structure M) (_ : Nonempty M), Theoryω.Model T M :=
  finitaryFragment_compact hT fun T₀ hT₀ hT₀fin => hfin T₀ hT₀ (hf_aFinite_iff.mpr hT₀fin)

/-- **Oracle condition 3, in full.**  Not merely the hypotheses separately: the *entire*
`CompactFor` statement holds over HF at the finitary fragment.

This is what certifies the interface — `hf_aFinite_iff` alone would leave open whether the
assembled statement still specializes.  Here it does, with no bridging lemma and no widening.

The `ACEnumerable` hypothesis is **discarded**, not used: the content is
`hf_compact_of_aFinite`.  So this theorem survives #19A tightening HF's `Sigma1` to the honest
c.e. predicate — it would then simply apply to fewer theories. -/
theorem hf_compactFor (T : Set L.Sentenceω) :
    CompactFor (hfPresentation L) (finitaryFragment L) T := fun hT _ hfin =>
  hf_compact_of_aFinite hT hfin

/-- **Gate 4.**  `CodedFamily` over HF is uninhabited. -/
theorem isEmpty_codedFamily_hf : IsEmpty (CodedFamily (hfPresentation L) n) :=
  ⟨fun F => F.infinitary⟩

/-- Consequently every upward-closure obligation over HF is vacuous, for **any** target set. -/
theorem hf_coded_closure_vacuous (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    ∀ F : CodedFamily (hfPresentation L) n,
      (∀ i, (⟨n, F.decode i⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ S) →
        (⟨n, codedIInf F⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ S :=
  fun F => absurd F.infinitary not_false


/-! ## Step 4 — the honest HF instance

Essentially a structure literal: the base is `hfFragment`, and both upward fields are closed by
certificate absurdity.  That it *is* nearly definitional is the signal that the signature is right. -/

/-- **The HF admissible fragment.**  No adapter, no widening. -/
def hfAdmissibleFragment (L : Language.{0, 0}) : AdmissibleFragment (hfPresentation L) where
  toFragment := hfFragment L
  iInf_coded_mem := fun F _ => absurd F.infinitary not_false
  iSup_coded_mem := fun F _ => absurd F.infinitary not_false

/-- **Oracle condition 1, at the interface level.**  The HF admissible fragment's underlying
`Fragment` is exactly `hfFragment`, whose sentence slice is `finitaryFragment`. -/
theorem hfAdmissibleFragment_toFragment (L : Language.{0, 0}) :
    (hfAdmissibleFragment L).toFragment = hfFragment L := rfl


/-! ## Universe gate — CLOSED

The structures are **language-indexed and universe-polymorphic**: `AdmissiblePresentation L` for
`L : Language.{u, v}`, so `AdmissiblePresentation L[[J]]` is well-formed for an arbitrary parameter
type `J`.  This is the generalization route, chosen over restricting the EM adapter to `J : Type 0`
— that restriction would silently weaken the existing arbitrary-target-order EM surface and confuse
a universe limitation with the later mathematical question of which template theories are genuinely
coded.

It does **not** claim a presentation for `L` lifts to one for `L[[J]]`; whether such a lift exists is
genuine #19A coding content.  Only the *signature* is settled here.

**Diagnosis of an earlier false alarm.**  A probe written with the result annotation `: Type` was
reported as a universe-plumbing blocker.  It was a bug in the probe, not the API: bare `Type` means
`Type 0`, and that result constraint propagates *backward*, forcing Lean to expect
`AdmissiblePresentation.{0,0,0,0}` and producing a misleading error on the presentation argument.
Explicit `.{…}` arguments cannot fix it, because the `Type 0` result constraint remains.  Writing
`Type _` (or `Sort _`) lets the presentation universes be inferred and both probes compile. -/

section UniverseGate

/-- Arbitrary parameter type, arbitrary language universes: a coded family elaborates. -/
example (Lb : Language.{u, v}) (J : Type w) (B : AdmissiblePresentation Lb[[J]]) (m : ℕ) : Type _ :=
  CodedFamily B m

/-- …and so does the fragment wrapper. -/
example (Lb : Language.{u, v}) (J : Type w) (B : AdmissiblePresentation Lb[[J]]) : Type _ :=
  AdmissibleFragment B

end UniverseGate

end FirstOrder.Language
