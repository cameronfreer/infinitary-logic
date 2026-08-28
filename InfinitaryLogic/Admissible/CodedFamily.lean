/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.Family

/-!
# The bare presentation signature (issue #18)

`AdmissiblePresentation` bundles the family layer with theory decoding and the bare `Sigma1`
predicate.  **The syntax layer no longer depends on it.**

`CodedFamily`, `codedIInf` and `codedISup` moved to `Admissible/Family.lean` and are parameterized
by `FamilyPresentation` — the minimal family view.  This file supplies the explicit projection
`AdmissiblePresentation.toFamilyPresentation`, which is how a full presentation is used with the
syntax layer during the staged #19A migration.

That direction matters: `Family.lean` is *imported by* this file, so a coded family cannot reach
`DecodesTheory` or `Sigma1` even in principle, and `scripts/check_family_cone.lean` keeps it that
way.  Previously the bundling was structural — one record carried both — and the boundary was a
matter of discipline rather than of types.
-/

namespace FirstOrder.Language

universe u v uCode uIndex

set_option linter.checkUnivs false in
/-- A **bare presentation signature**.  No admissible-set axioms yet — #19A fixes those.  What is
frozen here is which data the *theory* interface may depend on; the *syntax* interface depends only
on `toFamilyPresentation`. -/
structure AdmissiblePresentation (L : Language.{u, v}) where
  /-- Codes: the elements of `A` that name syntactic objects. -/
  Code : Type uCode
  /-- The index type a code names.  Comes *from the code*, never fixed at `ℕ`. -/
  Index : Code → Type uIndex
  /-- A code-determined enumeration.  Data, not a side condition: the `iInf` constructor is
  ℕ-indexed, so a family cannot be turned into syntax without one. -/
  indexEncodable : ∀ c, Encodable (Index c)
  /-- The certificate that a code names a genuinely **infinitary** family.  This is the predicate
  that is empty for HF. -/
  CodesInfFamily : Code → Prop
  /-- The decoding law: which family a code denotes. -/
  DecodesFamily : ∀ (n : ℕ) (c : Code), (Index c → L.BoundedFormulaω Empty n) → Prop
  /-- **Conditional functionality.**  An infinitary code determines its family.

  Conditioned on `CodesInfFamily` so HF discharges it **vacuously**.  Under
  `toFamilyPresentation` the condition is absorbed into the code subtype, where the corresponding
  law is unconditional. -/
  decodes_unique : ∀ {n : ℕ} {c : Code} {f g : Index c → L.BoundedFormulaω Empty n},
    CodesInfFamily c → DecodesFamily n c f → DecodesFamily n c g → f = g
  /-- Which set of sentences a code names.  A *theory* decoding, separate from `DecodesFamily`:
  the same codes (the elements of `A`) but a different thing named.  Being decoded by **some**
  code is exactly "`T₀ ∈ A`", the internality the Barwise theorem uses; there is deliberately no
  separate finiteness condition, because `A`-finite *means* `∈ A` and for `A = L(ω₁^CK)` that
  includes infinite hyperarithmetical sets. -/
  DecodesTheory : Code → Set L.Sentenceω → Prop
  /-- **Theory-decoding functionality.**  A code names *a* theory, not a family of them.  The
  companion to `decodes_unique`, and unconditional: unlike the family certificate there is no
  case here that any presentation should discharge vacuously. -/
  decodes_theory_unique : ∀ {c : Code} {T T' : Set L.Sentenceω},
    DecodesTheory c T → DecodesTheory c T' → T = T'
  /-- Σ₁-on-`A` definability of a theory.

  **A known placeholder, and the last bare external predicate here.**  It is exactly the shape
  this design rejects everywhere else — a `Prop` on an arbitrary external set, with no data
  witnessing the representation.  #19A replaces it with definition-code data; the honest
  replacement is built in `Admissible/Ambient.lean` and `Admissible/Numbering.lean`, and migration
  stage 5.3 installs it here.

  A presentation may set this to `True` to *widen* the compactness domain — HF does, to recover
  unrestricted first-order compactness — but that is an enlargement, not a Σ₁ claim. -/
  Sigma1 : Set L.Sentenceω → Prop

/-- **The projection to the syntax layer.**  Explicit, not a coercion: every site that builds
syntax from a full presentation should say so, since the point of the migration is to make those
sites visible and then shrink them. -/
def AdmissiblePresentation.toFamilyPresentation {L : Language.{u, v}}
    (A : AdmissiblePresentation.{u, v, uCode, uIndex} L) :
    FamilyPresentation.{u, v, uCode, uIndex} L where
  Element := A.Code
  IsFamilyCode := A.CodesInfFamily
  Index c := A.Index c.1
  indexEncodable c := A.indexEncodable c.1
  DecodesFamily n c f := A.DecodesFamily n c.1 f
  -- the old certificate hypothesis is exactly the subtype's second component
  decodes_unique {_ c _ _} hf hg := A.decodes_unique c.2 hf hg

@[simp] theorem AdmissiblePresentation.toFamilyPresentation_isFamilyCode
    {L : Language.{u, v}} (A : AdmissiblePresentation.{u, v, uCode, uIndex} L) :
    A.toFamilyPresentation.IsFamilyCode = A.CodesInfFamily := rfl

end FirstOrder.Language
