/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.WIP.HFFragment

/-!
# `CodedFamily` signature spike (issue #18, step 2)

Resolves the three Lean-level details before any `AdmissibleFragment` is written.  This is a
**signature** spike: `AdmissiblePresentation` is a bare interface with no axioms about admissible
sets — the point is to check that the *shapes* compose and that the HF oracle bites in the right
place.

## The three details, as implemented

1. **No independent arity.** `decode` lands in `BoundedFormulaω Empty n`, the structure's own `n`.
2. **The encoding is supplied by the presentation**, `indexEncodable`, keyed on the code — *not*
   found by instance search. `codedIInf` installs that specific encoding locally, so the syntax it
   builds is determined by the presentation's decoding of the code. An ambient `Encodable` instance
   for the same index type cannot change it.
3. **`infinitary : A.CodesInfFamily code` is a certificate**, and `decoded_by_code` ties `decode` to
   `code`. Without the certificate, any code with any decoding would build a `CodedFamily`.

## Where the HF oracle bites — a distinction worth stating precisely

`einf` pads with `⊤` internally to turn an `Encodable`-indexed family into the ℕ-indexed family the
`iInf` constructor wants. **That padding is fine** for a genuinely infinitary code.

The forbidden move is *granting `CodesInfFamily` to a finite HF code* and then using the padding to
manufacture a primitive `iInf`. So the oracle must bite at **the certificate**, not at the mechanics
of `einf`. For HF, `CodesInfFamily` is empty, hence `CodedFamily` is uninhabited, hence the upward
closure fields are vacuous — and no padding argument ever arises.
-/

namespace FirstOrder.Language

variable {L : Language.{0, 0}}

/-- A **bare presentation signature**.  No admissible-set axioms yet — #19A fixes those.  What is
frozen here is which data the fragment interface may depend on. -/
structure AdmissiblePresentation where
  /-- Codes: the elements of `A` that name syntactic objects. -/
  Code : Type
  /-- The index type a code names.  Comes *from the code*, never fixed at `ℕ`. -/
  Index : Code → Type
  /-- A code-determined enumeration.  Data, not a side condition: the `iInf` constructor is
  ℕ-indexed, so a family cannot be turned into syntax without one. -/
  indexEncodable : ∀ c, Encodable (Index c)
  /-- The certificate that a code names a genuinely **infinitary** family.  This is the predicate
  that is empty for HF. -/
  CodesInfFamily : Code → Prop
  /-- The decoding law: which family a code denotes. -/
  DecodesFamily : ∀ (L : Language.{0, 0}) (n : ℕ) (c : Code), (Index c → L.BoundedFormulaω Empty n) →
    Prop
  /-- **Conditional functionality.**  An infinitary code determines its family.  Without this,
  `DecodesFamily` is an arbitrary `Prop` and one code may admit many decodings, so `decoded_by_code`
  would constrain nothing and `codedIInf` would not be a function of the code.

  Conditioned on `CodesInfFamily` so HF discharges it **vacuously**; #19A fixes the fuller
  naturality laws. -/
  decodes_unique : ∀ {L : Language.{0, 0}} {n : ℕ} {c : Code}
    {f g : Index c → L.BoundedFormulaω Empty n},
    CodesInfFamily c → DecodesFamily L n c f → DecodesFamily L n c g → f = g

/-- A **coded family**: a code, its infinitary certificate, its decoded family, and the law tying
the two together. -/
structure CodedFamily (A : AdmissiblePresentation) (L : Language.{0, 0}) (n : ℕ) where
  code : A.Code
  infinitary : A.CodesInfFamily code
  decode : A.Index code → L.BoundedFormulaω Empty n
  decoded_by_code : A.DecodesFamily L n code decode

variable {A : AdmissiblePresentation} {n : ℕ}

/-- The conjunction a coded family names.  The encoding is the **presentation's**, installed
locally, so the resulting syntax depends on the code rather than on ambient instance search. -/
def codedIInf (F : CodedFamily A L n) : L.BoundedFormulaω Empty n :=
  letI : Encodable (A.Index F.code) := A.indexEncodable F.code
  BoundedFormulaω.einf F.decode

/-- The disjunction a coded family names. -/
def codedISup (F : CodedFamily A L n) : L.BoundedFormulaω Empty n :=
  letI : Encodable (A.Index F.code) := A.indexEncodable F.code
  BoundedFormulaω.esup F.decode

/-! ## Acceptance gates -/

section Gates

variable {M : Type} [L.Structure M] {v : Empty → M} {xs : Fin n → M}

/-- **Gate 1a.**  `codedIInf` realizes as a conjunction over `A.Index code`. -/
theorem realize_codedIInf (F : CodedFamily A L n) :
    (codedIInf F).Realize v xs ↔ ∀ i, (F.decode i).Realize v xs := by
  letI : Encodable (A.Index F.code) := A.indexEncodable F.code
  exact BoundedFormulaω.realize_einf F.decode

/-- **Gate 1b.**  …and `codedISup` as a disjunction. -/
theorem realize_codedISup (F : CodedFamily A L n) :
    (codedISup F).Realize v xs ↔ ∃ i, (F.decode i).Realize v xs := by
  letI : Encodable (A.Index F.code) := A.indexEncodable F.code
  exact BoundedFormulaω.realize_esup F.decode

end Gates

/-- **Gate 2.**  The arity is the parameter `n`; there is no independent arity field.  Stated as a
type ascription that would not elaborate if the arity could drift. -/
example (F : CodedFamily A L n) : L.BoundedFormulaω Empty n := codedIInf F

/-- **Gate 3.**  An alternative ambient `Encodable` on the index type cannot change the syntax.

The hypothesis `_e` is deliberately **unused**: it puts a competing instance in scope, and the
statement still holds by `rfl`, which is exactly the claim — `codedIInf` never consults instance
search, it reads `A.indexEncodable`. -/
theorem codedIInf_uses_presentation_encoding (F : CodedFamily A L n)
    (_e : Encodable (A.Index F.code)) :
    codedIInf F = (letI : Encodable (A.Index F.code) := A.indexEncodable F.code
      BoundedFormulaω.einf F.decode) := rfl

/-- **Gate 5 (functionality).**  The syntax built from a coded family is determined by the code:
two coded families with the same code have the same decoding, hence the same `codedIInf`. -/
theorem codedIInf_eq_of_code_eq {F G : CodedFamily A L n} (h : F.code = G.code) :
    codedIInf F = codedIInf G := by
  cases F with | mk c hinf f hf =>
  cases G with | mk c' hinf' g hg =>
  cases h
  cases A.decodes_unique hinf hf hg
  rfl

/-! ## Universe probe

The production structure will need `Language.{u, v}`; this spike fixes `Language.{0, 0}`.  The probe
below records what that costs today: the constant-expansion `L[[J]]` stays inside `Language.{0, 0}`
exactly when `J : Type 0`, which covers the `ℕ` used throughout the Henkin machinery — but an
arbitrary parameter type would raise the language universe and not fit. -/

section UniverseProbe

variable {A : AdmissiblePresentation}

/-- Fits: `L[[ℕ]]` is still `Language.{0, 0}`. -/
example (L : Language.{0, 0}) (n : ℕ) : Type := CodedFamily A L[[ℕ]] n

/-
**Does NOT fit**, verified by probe:

```
example (L : Language.{0,0}) (J : Type w) (n : ℕ) : Type := CodedFamily A L[[J]] n
--                                                                       ^ J : Type w
-- Application type mismatch: J has type Type w … but is expected to have type Type
```

`withConstants` is `Language.{max u w', v}`, so an arbitrary parameter type raises the language
universe out of `Language.{0, 0}`.

**Finding for step 3.**  The production `AdmissiblePresentation` must be generalized to
`Language.{u, v}` *before* the EM adapter is written — or the adapter must be constrained to
`J : Type 0`.  Deferring this past step 3 would bake the restriction into `AdmissibleFragment`.
-/

end UniverseProbe

/-! ## Gate 4 — the HF oracle

For HF the certificate is empty, so `CodedFamily` is uninhabited and the upward-closure fields of
any `AdmissibleFragment` over it are vacuous.  Note where the emptiness lives: in
`CodesInfFamily`, **not** in the index type's cardinality and **not** in `einf`'s padding. -/

/-- The HF presentation: codes are (say) natural numbers naming finite index types, and **no code
names an infinitary family**. -/
def hfPresentation : AdmissiblePresentation where
  Code := ℕ
  Index := fun k => Fin k
  indexEncodable := fun _ => inferInstance
  CodesInfFamily := fun _ => False
  DecodesFamily := fun _ _ _ _ => True
  -- vacuous: no code is infinitary
  decodes_unique := fun h _ _ => absurd h not_false

/-- **Gate 4.**  `CodedFamily` over HF is uninhabited. -/
theorem isEmpty_codedFamily_hf : IsEmpty (CodedFamily hfPresentation L n) :=
  ⟨fun F => F.infinitary⟩

/-- Consequently every upward-closure obligation over HF is vacuous, for **any** target set. -/
theorem hf_coded_closure_vacuous (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    ∀ F : CodedFamily hfPresentation L n,
      (∀ i, (⟨n, F.decode i⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ S) →
        (⟨n, codedIInf F⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ S :=
  fun F => absurd F.infinitary not_false

end FirstOrder.Language
