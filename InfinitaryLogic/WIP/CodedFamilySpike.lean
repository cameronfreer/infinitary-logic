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

universe u v uCode uIndex

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
  letI : Encodable (A.Index F.code) := A.indexEncodable F.code
  BoundedFormulaω.einf F.decode

/-- The disjunction a coded family names. -/
def codedISup (F : CodedFamily A n) : L.BoundedFormulaω Empty n :=
  letI : Encodable (A.Index F.code) := A.indexEncodable F.code
  BoundedFormulaω.esup F.decode

/-! ## Acceptance gates -/

section Gates

variable {M : Type} [L.Structure M] {v : Empty → M} {xs : Fin n → M}

/-- **Gate 1a.**  `codedIInf` realizes as a conjunction over `A.Index code`. -/
theorem realize_codedIInf (F : CodedFamily A n) :
    (codedIInf F).Realize v xs ↔ ∀ i, (F.decode i).Realize v xs := by
  letI : Encodable (A.Index F.code) := A.indexEncodable F.code
  exact BoundedFormulaω.realize_einf F.decode

/-- **Gate 1b.**  …and `codedISup` as a disjunction. -/
theorem realize_codedISup (F : CodedFamily A n) :
    (codedISup F).Realize v xs ↔ ∃ i, (F.decode i).Realize v xs := by
  letI : Encodable (A.Index F.code) := A.indexEncodable F.code
  exact BoundedFormulaω.realize_esup F.decode

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
    codedIInf F = (letI : Encodable (A.Index F.code) := A.indexEncodable F.code
      BoundedFormulaω.einf F.decode) := rfl

/-- **Gate 5 (functionality).**  The syntax built from a coded family is determined by the code:
two coded families with the same code have the same decoding, hence the same `codedIInf`. -/
theorem codedIInf_eq_of_code_eq {F G : CodedFamily A n} (h : F.code = G.code) :
    codedIInf F = codedIInf G := by
  cases F with | mk c hinf f hf =>
  cases G with | mk c' hinf' g hg =>
  cases h
  cases A.decodes_unique hinf hf hg
  rfl

/-! ## Universe probe

The structures are **language-indexed and universe-polymorphic**: `AdmissiblePresentation L` for
`L : Language.{u, v}`, so `AdmissiblePresentation L[[J]]` is well-formed for an arbitrary parameter
type `J`.  This is the generalization route, chosen over restricting the EM adapter to `J : Type 0`
— that restriction would silently weaken the existing arbitrary-target-order EM surface and confuse
a universe limitation with the later mathematical question of which template theories are genuinely
coded.

Note this does **not** claim a presentation for `L` lifts to one for `L[[J]]`; whether such a lift
exists is genuine #19A coding content.  Only the *signature* is settled here.

**Outstanding plumbing.**  A stand-alone probe `example … (B : AdmissiblePresentation Lb[[J]]) :
Type := CodedFamily B m` does not yet elaborate: Lean defaults `CodedFamily`'s universe arguments to
`0` instead of unifying them with the supplied presentation's, reporting
`expected AdmissiblePresentation.{0,0,0,0} ?m`.  That is use-site plumbing — explicit `.{…}`
application, or restructuring the binders — not a defect in the shape, since nothing here forces
`Type 0`.  Resolve it when the interface is promoted out of `WIP`, **before** the EM adapter. -/

/-! ## Gate 4 — the HF oracle

For HF the certificate is empty, so `CodedFamily` is uninhabited and the upward-closure fields of
any `AdmissibleFragment` over it are vacuous.  Note where the emptiness lives: in
`CodesInfFamily`, **not** in the index type's cardinality and **not** in `einf`'s padding. -/

/-- The HF presentation: codes are (say) natural numbers naming finite index types, and **no code
names an infinitary family**. -/
def hfPresentation (L : Language.{u, v}) : AdmissiblePresentation L where
  Code := ℕ
  Index := fun k => Fin k
  indexEncodable := fun _ => inferInstance
  CodesInfFamily := fun _ => False
  DecodesFamily := fun _ _ _ => True
  -- vacuous: no code is infinitary
  decodes_unique := fun h _ _ => absurd h not_false

/-- **Gate 4.**  `CodedFamily` over HF is uninhabited. -/
theorem isEmpty_codedFamily_hf : IsEmpty (CodedFamily (hfPresentation L) n) :=
  ⟨fun F => F.infinitary⟩

/-- Consequently every upward-closure obligation over HF is vacuous, for **any** target set. -/
theorem hf_coded_closure_vacuous (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    ∀ F : CodedFamily (hfPresentation L) n,
      (∀ i, (⟨n, F.decode i⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ S) →
        (⟨n, codedIInf F⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ S :=
  fun F => absurd F.infinitary not_false

/-! ## Step 3 — `AdmissibleFragment`

A **purely syntactic wrapper**: exactly three pieces.  No `height`, no compactness data.

* `height` is deferred because the contract has not settled whether it belongs to the presentation
  or is derived; a field here would permit a fragment whose height disagrees with its presentation's.
* Compactness is a *theorem with hypotheses*, proved externally — which is what makes
  "no theorem named Barwise compactness merely projects a field" structurally impossible. -/

/-- **An admissible fragment**: an ordinary `Fragment`, closed *upward* under the conjunctions and
disjunctions named by **certified** coded families — and under nothing else. -/
structure AdmissibleFragment {L : Language.{u, v}}
    (A : AdmissiblePresentation.{u, v, uCode, uIndex} L) extends Fragment L where
  iInf_coded_mem : ∀ {n : ℕ} (F : CodedFamily A n),
    (∀ i, (⟨n, F.decode i⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ toSet) →
      (⟨n, codedIInf F⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ toSet
  iSup_coded_mem : ∀ {n : ℕ} (F : CodedFamily A n),
    (∀ i, (⟨n, F.decode i⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ toSet) →
      (⟨n, codedISup F⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ toSet

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

end FirstOrder.Language
