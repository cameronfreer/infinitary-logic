/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.Family
import InfinitaryLogic.Lomega1omega.Theory

/-!
# The ambient presentation: one carrier, four kinds (issue #19A, steps 1–2)

The representation layer for a Barwise-style presentation.  **One** ambient `Element` type carries
*all* codes; the four kinds — family, theory, sentence, Σ-definition — are subdomains of it and may
overlap.  In the HF instance every code is a natural number, so they overlap totally.

## Why one carrier

Separate code sorts and a shared ambient type are inter-translatable (subtypes one way, `Sum` the
other), so this is not a question of expressiveness.  Two things decide it.

**KP closure discriminates.**  Pairing and union are operations on *elements*; they do not respect
the kind subdomains — the pair of a sentence code and a definition code is an element and typically
has no kind at all.  One carrier states such laws directly; separate sorts must route every closure
law through `Sum`.

**The frozen design is already ambient-shaped.**  `AdmissiblePresentation.Code` serves both
`DecodesFamily` and `DecodesTheory`: the same codes, a different thing named.

## What is derived rather than stored

`IsTheoryCode` and `decodeTheory` are **not** fields.  Given ambient membership, a theory code is
just an element all of whose members are sentence codes, and the theory it names is the decoded
image of those members.  Deriving them is what keeps `Mem` honest: a vacuous membership relation
would collapse the theory layer, which a stored `decodeTheory` field would hide.

Likewise `Sigma1` is derived from `enumerates`.  Because a Σ-definition code carries a set of
*sentence codes* and the theory it defines is their decoded **image**, functionality holds by
construction — see `AFinite.unique` and `Sigma1.unique`, both `h.trans h'.symm`.  There is no
extensionality law to discharge even though a sentence may have many codes.

**Totality is deliberately omitted.**  A presentation is not obliged to name every theory, and an
honest HF must not: `AFinite` is existential over codes, never a bijection with theories.

## The family layer is inherited, not duplicated

`AmbientPresentation` **extends `FamilyPresentation`**, so `Element` and `IsFamilyCode` — together
with the `Index` / `indexEncodable` / `DecodesFamily` / `decodes_unique` data the syntax layer needs
— come from the family view rather than being restated here.  That is what makes the ambient design
complete: before this, `IsFamilyCode` was an orphan field with no decoding data behind it, so no
coded family could actually be built from an ambient presentation.

The dependency runs one way.  `Admissible/Family.lean` does not import this file, so the syntax
layer cannot reach `decodeTheory`, `Sigma1`, `enumerates` or `WithKP`.

## Main definitions

- `AmbientPresentation`: the family view, ambient membership, the remaining kinds, and the
  decodings.
- `AmbientPresentation.decodeTheory`, `AFinite`: the theory layer, derived from membership.
- `AmbientPresentation.Sigma1`: the Σ-definition layer.
- `AmbientPresentation.AdequateFor`: the decoded sentence range is exactly the intended fragment.
- `AmbientPresentation.WithKP`: pairing and union, **with specification laws**.

## Main results

- `AmbientPresentation.subset_of_adequate`, `AmbientPresentation.AFinite.subset_of_adequate`:
  containment in the fragment is *derived* from adequacy, not assumed.
-/

namespace FirstOrder.Language

universe u v w uIndex

/-- **The ambient presentation.**  One carrier `Element`, an ambient membership relation, four
overlapping code kinds, and the decoding data.

`decodeSentence` is a *function*, so sentence decoding is functional by construction; it is not
injective, since a sentence may have many codes.  `enumerates` returns a set of **sentence codes**,
never a set of sentences — that is what makes `Sigma1` functional for free. -/
structure AmbientPresentation (L : Language.{u, v}) extends
    FamilyPresentation.{u, v, w, uIndex} L where
  /-- **Ambient membership.**  Without it, closure obligations are vacuous and the theory layer
  cannot be derived; see `WithKP`. -/
  Mem : Element → Element → Prop
  /-- Codes naming a single sentence. -/
  IsSentenceCode : Element → Prop
  /-- Codes naming a Σ-definition, i.e. an *intension*.  Contrast a theory code, which names a set
  of sentences extensionally. -/
  IsDefinitionCode : Element → Prop
  /-- **Stored** sentence decoding on the sentence-code subdomain. -/
  decodeSentence : {e // IsSentenceCode e} → L.Sentenceω
  /-- Which sentence codes a Σ-definition code enumerates.  Sets of *codes*, never of sentences. -/
  enumerates : {e // IsDefinitionCode e} → Set {e // IsSentenceCode e}

namespace AmbientPresentation

variable {L : Language.{u, v}} (A : AmbientPresentation.{u, v, w, uIndex} L)

/-- The sentence-code subdomain. -/
abbrev SentenceCode := {e // A.IsSentenceCode e}

/-- The Σ-definition-code subdomain. -/
abbrev DefinitionCode := {e // A.IsDefinitionCode e}

/-- The sentences the codes actually name. -/
def sentenceRange : Set L.Sentenceω := Set.range A.decodeSentence

/-! ### The theory layer, derived from membership -/

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

/-! ### The Σ-definition layer -/

/-- The theory a Σ-definition code defines: the decoded image of the sentence codes it
enumerates. -/
def theoryOf (d : A.DefinitionCode) : L.Theoryω := A.decodeSentence '' A.enumerates d

/-- **`A`-c.e.**, from the presentation's own coding data rather than an opaque predicate. -/
def Sigma1 (T : L.Theoryω) : Prop := ∃ d, A.theoryOf d = T

/-- Adequacy: the decoded sentence range is exactly the intended fragment. -/
def AdequateFor (F : Set L.Sentenceω) : Prop := A.sentenceRange = F

variable {A}

@[simp] theorem mem_decodeTheory {a : A.TheoryCode} {φ : L.Sentenceω} :
    φ ∈ A.decodeTheory a ↔ ∃ s : A.SentenceCode, A.Mem s.1 a.1 ∧ A.decodeSentence s = φ :=
  Iff.rfl

@[simp] theorem mem_theoryOf {d : A.DefinitionCode} {φ : L.Sentenceω} :
    φ ∈ A.theoryOf d ↔ ∃ s ∈ A.enumerates d, A.decodeSentence s = φ :=
  Iff.rfl

/-- **Functionality is free** — a theory code names an image, not a relation, so this needs no
extensionality law even though sentence decoding is non-injective. -/
theorem AFinite.unique {a : A.TheoryCode} {T T' : L.Theoryω}
    (h : A.decodeTheory a = T) (h' : A.decodeTheory a = T') : T = T' := h ▸ h'

/-- The same for the Σ-layer. -/
theorem Sigma1.unique {d : A.DefinitionCode} {T T' : L.Theoryω}
    (h : A.theoryOf d = T) (h' : A.theoryOf d = T') : T = T' := h ▸ h'

/-- Codes cannot name sentences outside the decoded range. -/
theorem decodeTheory_subset (a : A.TheoryCode) : A.decodeTheory a ⊆ A.sentenceRange := by
  rintro _ ⟨s, -, rfl⟩
  exact ⟨s, rfl⟩

/-- The same for the Σ-layer. -/
theorem theoryOf_subset (d : A.DefinitionCode) : A.theoryOf d ⊆ A.sentenceRange := by
  rintro _ ⟨s, -, rfl⟩
  exact ⟨s, rfl⟩

/-- **Containment, derived.**  `decodeTheory_subset` alone gives only a range bound; it becomes
containment in the fragment exactly when adequacy identifies that range. -/
theorem AFinite.subset_of_adequate {F : Set L.Sentenceω} (hade : A.AdequateFor F)
    {T : L.Theoryω} (hT : A.AFinite T) : T ⊆ F := by
  obtain ⟨a, rfl⟩ := hT
  exact hade ▸ decodeTheory_subset a

/-- **Containment for the Σ-layer, derived.**  This is what lets a presentation-relative
compactness wrapper discharge the `T ⊆ P` hypothesis internally, using the presentation's own
`Sigma1` rather than a free parameter. -/
theorem subset_of_adequate {F : Set L.Sentenceω} (hade : A.AdequateFor F)
    {T : L.Theoryω} (hT : A.Sigma1 T) : T ⊆ F := by
  obtain ⟨d, rfl⟩ := hT
  exact hade ▸ theoryOf_subset d

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
