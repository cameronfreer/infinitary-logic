/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.Family
import InfinitaryLogic.Lomega1omega.Theory

/-!
# The theory layer (issue #19A, migration stage 5.2)

The middle layer of the presentation tower:

```
FamilyPresentation        Element, IsFamilyCode, Index, DecodesFamily      -- syntax
        ↑
TheoryPresentation        + Mem, IsSentenceCode, decodeSentence
                          + derived IsTheoryCode / decodeTheory / AFinite  -- theories
        ↑
AmbientPresentation       + IsDefinitionCode, enumerates
                          + derived Sigma1                                 -- definability
```

**The theory API stops here.**  `AFinite` and `AFinitelySatisfiable` take a `TheoryPresentation`,
so at the *type* level they cannot mention definition codes, `Sigma1`, KP, or any numbering — those
are defined in files that import this one.  `scripts/check_theory_cone.lean` pins it.

That matters because the natural shortcut — define the production `AFinite` as
`AmbientPresentation.AFinite` — would have made the whole theory interface depend on the Σ layer
even though not one theory-side proof uses it.

## What is derived rather than stored

`IsTheoryCode` and `decodeTheory` are **not** fields.  Given ambient membership, a theory code is
just an element all of whose members are sentence codes, and the theory it names is the decoded
image of those members.  Deriving them is what keeps `Mem` honest: a vacuous membership relation
would collapse the theory layer, which a stored `decodeTheory` field would hide.

Functionality comes free: a theory code names an *image*, not a relation, so `AFinite.unique` is
`h ▸ h'` and no extensionality law is needed even though sentence decoding is non-injective.

**Totality is deliberately omitted.**  A presentation is not obliged to name every theory, and an
honest HF must not: `AFinite` is existential over codes, never a bijection with theories.

## Main definitions

- `TheoryPresentation`: the family view plus membership and sentence decoding.
- `TheoryPresentation.decodeTheory`, `AFinite`: the theory layer, derived from membership.
- `TheoryPresentation.AFinitelySatisfiable`: the Barwise premise.
- `TheoryPresentation.AdequateFor`: the decoded sentence range is exactly the intended fragment.

## Main results

- `TheoryPresentation.AFinite.subset_of_adequate`: containment in the fragment is *derived* from
  adequacy, not assumed.
-/

namespace FirstOrder.Language

universe u v w uIndex

/-- **The theory view of a presentation.**  The family view, plus ambient membership and sentence
decoding — and nothing about definability.

`decodeSentence` is a *function*, so sentence decoding is functional by construction; it is not
injective, since a sentence may have many codes. -/
structure TheoryPresentation (L : Language.{u, v}) extends
    FamilyPresentation.{u, v, w, uIndex} L where
  /-- **Ambient membership.**  Without it the theory layer cannot be derived and closure
  obligations are vacuous. -/
  Mem : Element → Element → Prop
  /-- Codes naming a single sentence. -/
  IsSentenceCode : Element → Prop
  /-- **Stored** sentence decoding on the sentence-code subdomain. -/
  decodeSentence : {e // IsSentenceCode e} → L.Sentenceω

namespace TheoryPresentation

variable {L : Language.{u, v}} (A : TheoryPresentation.{u, v, w, uIndex} L)

/-- The sentence-code subdomain. -/
abbrev SentenceCode := {e // A.IsSentenceCode e}

/-- The sentences the codes actually name. -/
def sentenceRange : Set L.Sentenceω := Set.range A.decodeSentence

/-- **Theory codes are derived, not stored**: an element all of whose members are sentence codes. -/
def IsTheoryCode (e : A.Element) : Prop := ∀ x, A.Mem x e → A.IsSentenceCode x

/-- The theory-code subdomain. -/
abbrev TheoryCode := {e // A.IsTheoryCode e}

/-- The sentence codes belonging to a theory code.  Well defined precisely because
`IsTheoryCode` says every member *is* a sentence code. -/
def members (a : A.TheoryCode) : Set A.SentenceCode := {s | A.Mem s.1 a.1}

/-- **The theory a code names**: the decoded image of its members. -/
def decodeTheory (a : A.TheoryCode) : L.Theoryω := A.decodeSentence '' A.members a

/-- **`A`-finiteness**: the theory is named by a theory code — Barwise's "`T₀ ∈ A`".

Not external finiteness.  It collapses to ordinary finiteness only at HF, and there only on the
finitary fragment; see `hfAmbient_aFinite_iff`. -/
def AFinite (T : L.Theoryω) : Prop := ∃ a : A.TheoryCode, A.decodeTheory a = T

/-- **The Barwise premise**: every `A`-finite subtheory is satisfiable.

Deliberately *not* `Theoryω.IsFinitelySatisfiable`, which quantifies over ordinarily finite
subtheories.  The two differ for every `A` beyond HF — `A`-finite means `∈ A`, so for
`A = L(ω₁^CK)` this quantifies over infinite hyperarithmetical subtheories as well. -/
def AFinitelySatisfiable (T : L.Theoryω) : Prop :=
  ∀ T₀ ⊆ T, A.AFinite T₀ → T₀.IsSatisfiable

/-- Adequacy: the decoded sentence range is exactly the intended fragment. -/
def AdequateFor (F : Set L.Sentenceω) : Prop := A.sentenceRange = F

variable {A}

@[simp] theorem mem_decodeTheory {a : A.TheoryCode} {φ : L.Sentenceω} :
    φ ∈ A.decodeTheory a ↔ ∃ s : A.SentenceCode, A.Mem s.1 a.1 ∧ A.decodeSentence s = φ :=
  Iff.rfl

/-- **Functionality is free** — a theory code names an image, not a relation, so this needs no
extensionality law even though sentence decoding is non-injective. -/
theorem AFinite.unique {a : A.TheoryCode} {T T' : L.Theoryω}
    (h : A.decodeTheory a = T) (h' : A.decodeTheory a = T') : T = T' := h ▸ h'

/-- Codes cannot name sentences outside the decoded range. -/
theorem decodeTheory_subset (a : A.TheoryCode) : A.decodeTheory a ⊆ A.sentenceRange := by
  rintro _ ⟨s, -, rfl⟩
  exact ⟨s, rfl⟩

/-- **Containment, derived.**  `decodeTheory_subset` alone gives only a range bound; it becomes
containment in the fragment exactly when adequacy identifies that range. -/
theorem AFinite.subset_of_adequate {F : Set L.Sentenceω} (hade : A.AdequateFor F)
    {T : L.Theoryω} (hT : A.AFinite T) : T ⊆ F := by
  obtain ⟨a, rfl⟩ := hT
  exact hade ▸ decodeTheory_subset a

end TheoryPresentation

end FirstOrder.Language
