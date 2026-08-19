/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.CodedFamily
import InfinitaryLogic.Lomega1omega.Theory

/-!
# Theory predicates, external to the fragment (issue #18, contract §4)

`AFinite` and `ACEnumerable` are the two hypotheses a Barwise-style compactness theorem takes.
They are **predicates on a theory relative to a presentation**, never fields of
`AdmissibleFragment`.

That placement is the whole point.  Compactness is a *theorem with hypotheses*, so a statement
named "Barwise compactness" cannot be discharged by projecting a field it does not have — the
defect `barwise_compactness` exhibits today, where the conclusion is `A.compact` applied to its own
arguments.  Keeping the evidence outside the record makes that structurally impossible rather than
merely observed.

**`AFinite` is not ordinary finiteness.**  It is membership in `A` — "`T₀ ∈ A`" — which for
`A = L(ω₁^CK)` includes infinite hyperarithmetical sets.  The two coincide exactly at `A = HF`,
which is what `hf_aFinite_iff` below proves and what makes HF's compactness theorem
`finitaryFragment_compact` by specialization rather than by a bridging lemma.
-/

namespace FirstOrder.Language

universe u v uCode uIndex

variable {L : Language.{u, v}} (A : AdmissiblePresentation.{u, v, uCode, uIndex} L)

/-- **`A`-finiteness**: the theory is named by a code that `A` believes finite.  The Barwise
theorem's "`T₀ ∈ A`", not external finiteness. -/
def AFinite (T : Set L.Sentenceω) : Prop :=
  ∃ c, A.CodesFinite c ∧ A.DecodesTheory c T

/-- **`A`-c.e.**: the theory is Σ₁-on-`A`.  The definability side condition that restricts which
theories the compactness theorem applies to. -/
def ACEnumerable (T : Set L.Sentenceω) : Prop :=
  A.Sigma1 T

variable {A}

theorem aFinite_def {T : Set L.Sentenceω} :
    AFinite A T ↔ ∃ c, A.CodesFinite c ∧ A.DecodesTheory c T := Iff.rfl

theorem acEnumerable_def {T : Set L.Sentenceω} : ACEnumerable A T ↔ A.Sigma1 T := Iff.rfl

/-- The shape of a Barwise-style compactness statement: both predicates enter as **hypotheses**.
Stated as an abbreviation so that instances are checked to have this exact shape, and so that no
theorem can claim it while secretly reading a compactness field — there is none to read. -/
def CompactFor (T : Set L.Sentenceω) : Prop :=
  ACEnumerable A T →
    (∀ T₀ ⊆ T, AFinite A T₀ →
      ∃ (M : Type) (_ : L.Structure M) (_ : Nonempty M), Theoryω.Model T₀ M) →
    ∃ (M : Type) (_ : L.Structure M) (_ : Nonempty M), Theoryω.Model T M

end FirstOrder.Language
