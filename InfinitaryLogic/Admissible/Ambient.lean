/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.Theory

/-!
# The ambient presentation: the definability layer (issue #19A)

The top of the presentation tower.  **One** ambient `Element` type carries *all* codes; the four
kinds — family, theory, sentence, Σ-definition — are subdomains of it and may overlap.  In the HF
instance every code is a natural number, so they overlap totally.

```
FamilyPresentation     Element, IsFamilyCode, Index, DecodesFamily      -- Admissible/Family.lean
        ↑
TheoryPresentation     + Mem, IsSentenceCode, decodeSentence            -- Admissible/Theory.lean
                       + derived IsTheoryCode / decodeTheory / AFinite
        ↑
AmbientPresentation    + IsDefinitionCode, enumerates                   -- this file
                       + derived Sigma1
```

Each layer is a separate file and each is imported *by* the next, so the syntax layer cannot reach
the theory layer and the theory layer cannot reach definability — not by convention, by types and
imports.  `scripts/check_family_cone.lean` and `scripts/check_theory_cone.lean` pin both.

## Why one carrier

Separate code sorts and a shared ambient type are inter-translatable (subtypes one way, `Sum` the
other), so this is not a question of expressiveness.  Two things decide it.

**KP closure discriminates.**  Pairing and union are operations on *elements*; they do not respect
the kind subdomains — the pair of a sentence code and a definition code is an element and typically
has no kind at all.  One carrier states such laws directly; separate sorts must route every closure
law through `Sum`.

**One carrier was always the intent.**  The same codes — the elements of `A` — serve the family,
theory, sentence and Σ-definition roles; only the thing named differs.

## `Sigma1` is derived

Because a Σ-definition code carries a set of *sentence codes* and the theory it defines is their
decoded **image**, functionality holds by construction — `Sigma1.unique` is `h ▸ h'`.  There is no
extensionality law to discharge even though a sentence may have many codes.

## Main definitions

- `AmbientPresentation`: the theory view plus the Σ-definition kind.
- `AmbientPresentation.Sigma1`: the definability layer.
- `AmbientPresentation.WithKP`: pairing and union, **with specification laws**.

## Main results

- `AmbientPresentation.subset_of_adequate`: fragment containment for Σ-definable theories, derived
  from adequacy rather than assumed.
-/

namespace FirstOrder.Language

universe u v w uIndex

/-- **The ambient presentation.**  The theory view plus the Σ-definition kind.

`enumerates` returns a set of **sentence codes**, never a set of sentences — that is what makes
`Sigma1` functional for free. -/
structure AmbientPresentation (L : Language.{u, v}) extends
    TheoryPresentation.{u, v, w, uIndex} L where
  /-- Codes naming a Σ-definition, i.e. an *intension*.  Contrast a theory code, which names a set
  of sentences extensionally. -/
  IsDefinitionCode : Element → Prop
  /-- Which sentence codes a Σ-definition code enumerates.  Sets of *codes*, never of sentences. -/
  enumerates : {e // IsDefinitionCode e} → Set {e // IsSentenceCode e}

namespace AmbientPresentation

variable {L : Language.{u, v}} (A : AmbientPresentation.{u, v, w, uIndex} L)

/-- The Σ-definition-code subdomain. -/
abbrev DefinitionCode := {e // A.IsDefinitionCode e}

/-- The theory a Σ-definition code defines: the decoded image of the sentence codes it
enumerates. -/
def theoryOf (d : A.DefinitionCode) : L.Theoryω := A.decodeSentence '' A.enumerates d

/-- **`A`-c.e.**, from the presentation's own coding data rather than an opaque predicate. -/
def Sigma1 (T : L.Theoryω) : Prop := ∃ d, A.theoryOf d = T

variable {A}

@[simp] theorem mem_theoryOf {d : A.DefinitionCode} {φ : L.Sentenceω} :
    φ ∈ A.theoryOf d ↔ ∃ s ∈ A.enumerates d, A.decodeSentence s = φ :=
  Iff.rfl

/-- **Functionality is free** — the theory is an image, not a relation. -/
theorem Sigma1.unique {d : A.DefinitionCode} {T T' : L.Theoryω}
    (h : A.theoryOf d = T) (h' : A.theoryOf d = T') : T = T' := h ▸ h'

/-- Σ-definable theories cannot escape the decoded range. -/
theorem theoryOf_subset (d : A.DefinitionCode) : A.theoryOf d ⊆ A.sentenceRange := by
  rintro _ ⟨s, -, rfl⟩
  exact ⟨s, rfl⟩

/-- **Containment for the Σ-layer, derived.**  This is what lets a presentation-relative
compactness wrapper discharge the `T ⊆ P` hypothesis internally, using the presentation's own
`Sigma1` rather than a free parameter. -/
theorem subset_of_adequate {F : Set L.Sentenceω} (hade : A.AdequateFor F)
    {T : L.Theoryω} (hT : A.Sigma1 T) : T ⊆ F := by
  obtain ⟨d, rfl⟩ := hT
  exact hade ▸ theoryOf_subset d

/-! ### The compactness interface

Both come from the presentation's own definition codes, rather than from a bare external `Sigma1`
predicate carrying no representation data. -/

variable (A)

/-- **`A`-c.e.**: the theory is Σ₁-on-`A`.

Unlike the legacy predicate this is not an arbitrary `Prop` on a set — unfolding it produces a
definition *code*, which is what makes `subset_of_adequate` available at all. -/
def ACEnumerable (T : L.Theoryω) : Prop := A.Sigma1 T

/-- The shape of a Barwise-style compactness statement over a permitted sentence set `P`.

`T ⊆ P` stays a **genuine hypothesis**.  It is not removed: `subset_of_adequate` yields it only
once an adequacy equation identifies the decoded range with `P`, and a presentation need not be
adequate for the `P` a caller has in mind.  `compactFor_of_adequate` below is the wrapper that
discharges it where adequacy *is* available.

Both premises enter as hypotheses, so no instance can claim this shape while secretly projecting a
compactness field — there is none to read. -/
def CompactFor (P T : L.Theoryω) : Prop :=
  T ⊆ P → A.ACEnumerable T → A.toTheoryPresentation.AFinitelySatisfiable T → T.IsSatisfiable

variable {A}

theorem acEnumerable_def {T : L.Theoryω} : A.ACEnumerable T ↔ A.Sigma1 T := Iff.rfl

/-- **The assembly theorem.**  A consumer holding compactness *and* adequacy never supplies
containment: it follows from Σ-definability, because a definition code enumerates sentence codes
and those decode into the fragment and nowhere else.

This is the payoff of `Sigma1` carrying coding data rather than being a bare predicate — the legacy
route could not state it. -/
theorem compactFor_of_adequate {P T : L.Theoryω} (hcompact : A.CompactFor P T)
    (hade : A.AdequateFor P) (hce : A.ACEnumerable T)
    (hfin : A.toTheoryPresentation.AFinitelySatisfiable T) : T.IsSatisfiable :=
  hcompact (subset_of_adequate hade hce) hce hfin

/-! ### KP closure, with specification laws -/

/-- **Pairing and union, stated meaningfully.**

The earlier sketch carried only totality — `pair_total : ∀ a b, ∃ c, Pair a b c` — which is
satisfied by `Pair := fun _ _ _ => True` on any inhabited carrier.  **Totality is not pairing.**
Here each operation is pinned by a specification law against `Mem`, so the fields cannot be
discharged trivially.

Only pairing and union appear.  The full KP schema is deliberately not attempted: the #19A source
audit must first identify which closure and absoluteness laws later proofs actually consume. -/
structure WithKP (L : Language.{u, v}) extends AmbientPresentation.{u, v, w, uIndex} L where
  /-- The unordered pair. -/
  pair : Element → Element → Element
  /-- Its specification — the law the bare totality field lacked. -/
  mem_pair : ∀ a b x, Mem x (pair a b) ↔ x = a ∨ x = b
  /-- The union. -/
  union : Element → Element
  /-- Its specification. -/
  mem_union : ∀ a x, Mem x (union a) ↔ ∃ y, Mem y a ∧ Mem x y

end AmbientPresentation

end FirstOrder.Language
