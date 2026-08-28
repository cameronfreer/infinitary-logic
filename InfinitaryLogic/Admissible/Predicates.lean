/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.CodedFamily
import InfinitaryLogic.Admissible.Theory

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
ones.  Being named by a code *is* the condition.

## Two routes, during the #19A migration

The production `A`-finiteness predicates now live on the **theory view**, as
`TheoryPresentation.AFinite` and `TheoryPresentation.AFinitelySatisfiable`
(`Admissible/Theory.lean`).  They are derived from ambient membership and cannot mention
definition codes or `Sigma1` at the type level.

What remains here is the **legacy route**, namespaced under `AdmissiblePresentation` so every use
site says so.  It is kept only because `Sigma1` is still a bare external predicate on that
structure; migration stage 5.3 replaces it with definition-code data, and stage 5.4 retires these
declarations along with `hfPresentation`.

The legacy route has no `toTheoryPresentation`, and that is not an oversight:
`AdmissiblePresentation` stores `DecodesTheory` as an arbitrary relation and has no `Mem` or
`decodeSentence`, so there is nothing to derive a theory view *from*.  The absence is the honest
statement of how far the migration has got.
-/

namespace FirstOrder.Language

universe u v uCode uIndex

variable {L : Language.{u, v}} (A : AdmissiblePresentation.{u, v, uCode, uIndex} L)

/-! ## The legacy route (retired in migration stage 5.4) -/

/-- **`A`-finiteness**, legacy form: the theory is named by a code, via the stored `DecodesTheory`
relation rather than derived from membership. -/
def AdmissiblePresentation.AFinite (T : Set L.Sentenceω) : Prop :=
  ∃ c, A.DecodesTheory c T

/-- **`A`-c.e.**: the theory is Σ₁-on-`A`.  The definability side condition that restricts which
theories the compactness theorem applies to.

Still a bare external predicate — this is exactly what stage 5.3 replaces. -/
def AdmissiblePresentation.ACEnumerable (T : Set L.Sentenceω) : Prop :=
  A.Sigma1 T

variable {A}

theorem AdmissiblePresentation.aFinite_def {T : Set L.Sentenceω} :
    A.AFinite T ↔ ∃ c, A.DecodesTheory c T := Iff.rfl

theorem AdmissiblePresentation.acEnumerable_def {T : Set L.Sentenceω} :
    A.ACEnumerable T ↔ A.Sigma1 T := Iff.rfl

/-- A code names at most one `A`-finite theory — `decodes_theory_unique` at the predicate level. -/
theorem AdmissiblePresentation.AFinite.unique {T T' : Set L.Sentenceω} {c : A.Code}
    (h : A.DecodesTheory c T) (h' : A.DecodesTheory c T') : T = T' :=
  A.decodes_theory_unique h h'

variable (A)

/-- **The Barwise premise**, legacy form: every `A`-finite subtheory is satisfiable.

Deliberately *not* `Theoryω.IsFinitelySatisfiable`, which quantifies over ordinarily finite
subtheories.  The two differ for every `A` beyond HF. -/
def AdmissiblePresentation.AFinitelySatisfiable (T : L.Theoryω) : Prop :=
  ∀ T₀ ⊆ T, A.AFinite T₀ → T₀.IsSatisfiable

/-- The shape of a Barwise-style compactness statement, over a permitted sentence set `P`.

`T ⊆ P` is a genuine hypothesis, not decoration: the standard theorem restricts to theories inside
the fragment `L_A`.  Both predicates enter as hypotheses too, so no instance can claim this shape
while secretly reading a compactness field — there is none to read.

Legacy, because `ACEnumerable` is: the honest replacement uses the presentation's own definability
data and derives `T ⊆ P` from adequacy (`AmbientPresentation.subset_of_adequate`). -/
def AdmissiblePresentation.CompactFor (P T : L.Theoryω) : Prop :=
  T ⊆ P → A.ACEnumerable T → A.AFinitelySatisfiable T → T.IsSatisfiable

end FirstOrder.Language
