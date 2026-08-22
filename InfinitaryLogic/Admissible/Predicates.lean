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

**`A`-finite means `T₀ ∈ A`, nothing more.**  It is not "`A` believes `T₀` finite", and it is not
external finiteness: for `A = L(ω₁^CK)` the `A`-finite sets include infinite hyperarithmetical
ones.  Being named by a code *is* the condition.  It collapses to ordinary finiteness exactly at
`A = HF`, which is what `hf_aFinite_iff` proves and what makes HF's compactness statement
`finitaryFragment_compact` by specialization rather than by a bridging lemma.
-/

namespace FirstOrder.Language

universe u v uCode uIndex

variable {L : Language.{u, v}} (A : AdmissiblePresentation.{u, v, uCode, uIndex} L)

/-- **`A`-finiteness**: the theory is named by a code — the Barwise theorem's "`T₀ ∈ A`".  No
finiteness side condition; see the module docstring. -/
def AFinite (T : Set L.Sentenceω) : Prop :=
  ∃ c, A.DecodesTheory c T

/-- **`A`-c.e.**: the theory is Σ₁-on-`A`.  The definability side condition that restricts which
theories the compactness theorem applies to. -/
def ACEnumerable (T : Set L.Sentenceω) : Prop :=
  A.Sigma1 T

variable {A}

theorem aFinite_def {T : Set L.Sentenceω} : AFinite A T ↔ ∃ c, A.DecodesTheory c T := Iff.rfl

theorem acEnumerable_def {T : Set L.Sentenceω} : ACEnumerable A T ↔ A.Sigma1 T := Iff.rfl

/-- A code names at most one `A`-finite theory — `decodes_theory_unique` at the predicate level. -/
theorem AFinite.unique {T T' : Set L.Sentenceω} {c : A.Code}
    (h : A.DecodesTheory c T) (h' : A.DecodesTheory c T') : T = T' :=
  A.decodes_theory_unique h h'

variable (A)

/-- **The Barwise premise**: every `A`-finite subtheory is satisfiable.

Deliberately *not* `Theoryω.IsFinitelySatisfiable`, which quantifies over ordinarily finite
subtheories.  The two differ for every `A` beyond HF — `A`-finite means `∈ A`, so for
`A = L(ω₁^CK)` this quantifies over infinite hyperarithmetical subtheories as well.  Naming both
is what makes the confusion hard to commit silently. -/
def AFinitelySatisfiable (T : L.Theoryω) : Prop :=
  ∀ T₀ ⊆ T, AFinite A T₀ → T₀.IsSatisfiable

/-- The shape of a Barwise-style compactness statement, over a permitted sentence set `P`.

`T ⊆ P` is a genuine hypothesis, not decoration: the standard theorem restricts to theories inside
the fragment `L_A`.  Both predicates enter as hypotheses too, so no instance can claim this shape
while secretly reading a compactness field — there is none to read. -/
def CompactFor (P T : L.Theoryω) : Prop :=
  T ⊆ P → ACEnumerable A T → AFinitelySatisfiable A T → T.IsSatisfiable

end FirstOrder.Language
