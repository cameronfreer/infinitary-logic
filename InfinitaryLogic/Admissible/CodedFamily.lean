/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Syntax
import InfinitaryLogic.Lomega1omega.Semantics

/-!
# Coded families over an admissible presentation (issue #18)

The honest replacement for closure under *arbitrary external* ℕ-indexed families.  A fragment may
only be asked to contain the conjunctions and disjunctions that the admissible set itself **names**.

Three details are load-bearing and each was validated against the HF instance before being fixed:

1. `decode` lands in the structure's own arity — no independent arity field can drift.
2. The enumeration is supplied by the presentation (`indexEncodable`), keyed on the code, **not**
   found by instance search; the syntax a coded family builds therefore depends on the code.
3. `infinitary` is a **certificate**.  Without it any code with any decoding would build a coded
   family, and "HF has no primitive coded families" would be unstatable.

`decodes_unique` makes decoding code-determined, which is what the extensionality API below rests
on.  Fuller naturality laws are #19A's business.
-/

namespace FirstOrder.Language

universe u v w uCode uIndex

set_option linter.checkUnivs false in
/-- A **bare presentation signature**.  No admissible-set axioms yet — #19A fixes those.  What is
frozen here is which data the fragment interface may depend on. -/
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
  /-- **Conditional functionality.**  An infinitary code determines its family.  Without this,
  `DecodesFamily` is an arbitrary `Prop` and one code may admit many decodings, so `decoded_by_code`
  would constrain nothing and `codedIInf` would not be a function of the code.

  Conditioned on `CodesInfFamily` so HF discharges it **vacuously**; #19A fixes the fuller
  naturality laws. -/
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
  witnessing the representation — and it is retained only because carrying the defining Σ formula
  needs the Δ₀/Σ hierarchy for the `∈`-language.  #19A replaces it with decoding data
  (`DefinesSigmaTheory : DefinitionCode → Set L.Sentenceω → Prop` plus a uniqueness law); whether
  `DefinitionCode` is the same carrier as `Code` is an audit question, since making the carrier
  explicit does not require conflating unrelated kinds of code.

  A presentation may set this to `True` to *widen* the compactness domain — HF does, to recover
  unrestricted first-order compactness — but that is an enlargement, not a Σ₁ claim. -/
  Sigma1 : Set L.Sentenceω → Prop

/-- A **coded family**: a code, its infinitary certificate, its decoded family, and the law tying
the two together. -/
structure CodedFamily {L : Language.{u, v}} (A : AdmissiblePresentation.{u, v, uCode, uIndex} L)
    (n : ℕ) where
  code : A.Code
  infinitary : A.CodesInfFamily code
  decode : A.Index code → L.BoundedFormulaω Empty n
  decoded_by_code : A.DecodesFamily n code decode

variable {L : Language.{u, v}} {A : AdmissiblePresentation.{u, v, uCode, uIndex} L} {n : ℕ}

/-- The conjunction a coded family names.  The encoding is the **presentation's**, installed
locally, so the resulting syntax depends on the code rather than on ambient instance search. -/
def codedIInf (F : CodedFamily A n) : L.BoundedFormulaω Empty n :=
  BoundedFormulaω.einfWith (A.indexEncodable F.code) F.decode

/-- The disjunction a coded family names. -/
def codedISup (F : CodedFamily A n) : L.BoundedFormulaω Empty n :=
  BoundedFormulaω.esupWith (A.indexEncodable F.code) F.decode

/-! ## Acceptance gates -/

section Gates

variable {M : Type} [L.Structure M] {v : Empty → M} {xs : Fin n → M}

/-- **Gate 1a.**  `codedIInf` realizes as a conjunction over `A.Index code`. -/
theorem realize_codedIInf (F : CodedFamily A n) :
    (codedIInf F).Realize v xs ↔ ∀ i, (F.decode i).Realize v xs :=
  BoundedFormulaω.realize_einfWith _ F.decode

/-- **Gate 1b.**  …and `codedISup` as a disjunction. -/
theorem realize_codedISup (F : CodedFamily A n) :
    (codedISup F).Realize v xs ↔ ∃ i, (F.decode i).Realize v xs :=
  BoundedFormulaω.realize_esupWith _ F.decode

end Gates

/-- **Gate 2.**  The arity is the parameter `n`; there is no independent arity field.  Stated as a
type ascription that would not elaborate if the arity could drift. -/
example (F : CodedFamily A n) : L.BoundedFormulaω Empty n := codedIInf F

/-- **Gate 3.**  An alternative ambient `Encodable` on the index type cannot change the syntax.

The hypothesis `_e` is deliberately **unused**: it puts a competing instance in scope, and the
statement still holds by `rfl`, which is exactly the claim — `codedIInf` never consults instance
search, it reads `A.indexEncodable`. -/
theorem codedIInf_uses_presentation_encoding (F : CodedFamily A n)
    (_e : Encodable (A.Index F.code)) :
    codedIInf F = BoundedFormulaω.einfWith (A.indexEncodable F.code) F.decode := rfl

/-! ### Extensionality

Conditional functionality (`decodes_unique`) is what makes a coded family *determined by its code*.
Everything below is a consequence, and it is what keeps #19A's naturality layer from having to
re-derive uniqueness at every step. -/

/-- Equal codes force equal decodings. -/
theorem decode_eq_of_code_eq {F G : CodedFamily A n} (h : F.code = G.code) :
    F.decode = h ▸ G.decode := by
  cases F with | mk c hinf f hf =>
  cases G with | mk c' hinf' g hg =>
  cases h
  exact A.decodes_unique hinf hf hg

/-- **Extensionality**: a coded family is its code.  The certificate and the decoding law are
`Prop`s, and the decoding is determined by the code, so nothing else can differ. -/
@[ext] theorem CodedFamily.ext {F G : CodedFamily A n} (h : F.code = G.code) : F = G := by
  cases F with | mk c hinf f hf =>
  cases G with | mk c' hinf' g hg =>
  cases h
  cases A.decodes_unique hinf hf hg
  rfl

/-- **Gate 5 (functionality).**  The conjunction built from a coded family is determined by the
code. -/
theorem codedIInf_eq_of_code_eq {F G : CodedFamily A n} (h : F.code = G.code) :
    codedIInf F = codedIInf G := by rw [CodedFamily.ext h]

/-- …and the disjunction likewise. -/
theorem codedISup_eq_of_code_eq {F G : CodedFamily A n} (h : F.code = G.code) :
    codedISup F = codedISup G := by rw [CodedFamily.ext h]

end FirstOrder.Language
