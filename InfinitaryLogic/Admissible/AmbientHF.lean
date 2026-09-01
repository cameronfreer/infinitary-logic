/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.Ambient
import InfinitaryLogic.Admissible.Ackermann
import InfinitaryLogic.Admissible.HF
import Mathlib.Computability.PartrecCode

/-!
# The honest HF ambient instance (issue #19A)

`Element := ℕ` under Ackermann membership.  Sentence codes are the `enc`-image of the *finitary*
sentences, theory codes are exactly the finite sets of sentence codes, and pairing and union are
ordinary arithmetic.  The four kinds **overlap**, which is correct: in HF every code is a number.

## `A`-finiteness is *not* plain finiteness

Theory codes are built from **finitary** sentence codes, so a finite theory containing an
infinitary sentence is not an element of HF.  The characterization is `hfAmbient_aFinite_iff`:

```
AFinite T ↔ T.Finite ∧ T ⊆ finitaryFragment L
```

with `hfAmbient_aFinite_iff_of_finitary` as the consumer-friendly form.  Both conjuncts are
necessary: encoding arbitrary infinitary sentences into HF is ruled out by the uncountability of
`L.Sentenceω` (`docs/admissible-19a-checkpoint.md` §1).  `not_hfAmbient_aFinite_iff_finite`
exhibits a finite non-`A`-finite theory rather than merely asserting the distinction.

## What injectivity does and does not give

`FinitaryCoding` stores an injective numbering.  Injectivity gives numbering-independence of the
decoded *range* — hence of adequacy and containment, which is `hfAmbient_range_indep` — but **not**
of `Sigma1`: two injective numberings can disagree about which theories are c.e.  `Sigma1`
invariance is a separate layer, and holds only against an explicit `ComputablyEquivalent` witness;
see `Admissible/Numbering.lean`.

## Main definitions

- `FinitaryCoding`: the **stored** finitary-sentence numbering.
- `hfAmbient`: the ambient presentation at `Element := ℕ`.
- `hfAmbientKP`: its pairing and union, discharged by Ackermann arithmetic.

## Main results

- `hfAmbient_adequate`: the sentence codes decode onto exactly `finitaryFragment L`.
- `hfAmbient_aFinite_iff`: the corrected `A`-finiteness characterization.
- `hfAmbient_compact`: the assembled regression, with containment discharged internally.
-/

namespace FirstOrder.Language

universe u v

open scoped Nat

variable (L)

/-- **The stored coding.**  Not `[Encodable L.Sentence]`: an ambient instance is chosen by
instance search and gives no invariance between numberings, so the encoding is carried as data.
Same lesson as `codedIInf_uses_presentation_encoding`. -/
structure FinitaryCoding (L : Language.{u, v}) where
  /-- The numbering of finitary sentences. -/
  enc : L.Sentence → ℕ
  /-- Injectivity — enough for range-invariance, **not** enough for `Sigma1`-invariance. -/
  enc_injective : Function.Injective enc

variable {L}

/-- **The honest HF ambient presentation**, relative to a stored coding.

`noncomputable` only because `decodeSentence` inverts `enc` by choice; the *coding* itself is
concrete data, which is the point of storing it. -/
noncomputable def hfAmbient (C : FinitaryCoding L) : AmbientPresentation.{u, v, 0, 0} L where
  Element := ℕ
  -- Ackermann membership: `x ∈ₐ e` iff bit `x` of `e` is set
  Mem := Nat.AckMem
  -- **no code names an infinitary family** — the sole source of HF's coded-family emptiness.
  -- Everything below it in the family layer is then vacuous: the code subdomain is empty, so
  -- `Index`, `indexEncodable`, `DecodesFamily` and functionality are all `c.2.elim`.
  IsFamilyCode _ := False
  Index c := c.2.elim
  indexEncodable c := c.2.elim
  DecodesFamily _ c _ := c.2.elim
  decodes_unique {_} {c} {_} {_} _ _ := c.2.elim
  IsSentenceCode n := ∃ φ₀ : L.Sentence, C.enc φ₀ = n
  -- every natural reads as a partial-recursive code
  IsDefinitionCode _ := True
  decodeSentence e := e.2.choose.toLω
  enumerates d := {s | (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code d.1) s.1).Dom}

/-- **The ambient instance and the family-layer HF presentation agree, definitionally.**

`hfFamily` is what the HF *syntax* consumers (`isEmpty_codedFamily_hf`, `hf_coded_closure_vacuous`,
`hfAdmissibleFragment`) are stated over, and this is what ties them to the ambient instance without
either one depending on the other's extra layers.  It is also independent of the coding `C`, as it
must be: the family layer sees no sentence numbering. -/
theorem hfAmbient_toFamilyPresentation (C : FinitaryCoding L) :
    (hfAmbient C).toFamilyPresentation = hfFamily L := rfl

/-- Decoding a stored code returns that very sentence — this is where `enc_injective` is used, and
why the coding must be stored rather than assumed. -/
theorem hfAmbient_decode (C : FinitaryCoding L) (φ₀ : L.Sentence)
    (h : (hfAmbient C).IsSentenceCode (C.enc φ₀)) :
    (hfAmbient C).decodeSentence ⟨C.enc φ₀, h⟩ = φ₀.toLω :=
  congrArg _ (C.enc_injective h.choose_spec)

/-- **Adequacy: the HF sentence codes decode onto exactly `finitaryFragment L`.** -/
theorem hfAmbient_adequate (C : FinitaryCoding L) :
    (hfAmbient C).AdequateFor (finitaryFragment L) := by
  ext φ
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e.2.choose, rfl⟩
  · rintro ⟨φ₀, rfl⟩
    exact ⟨⟨C.enc φ₀, φ₀, rfl⟩, hfAmbient_decode C φ₀ _⟩

/-- **Numbering invariance, stated the only way it can be.**  The decoded range is
`finitaryFragment L` for *every* stored coding, so adequacy — and hence containment — does not
depend on which numbering was chosen.

What is **not** claimed is that `Sigma1` is numbering-invariant; that needs acceptable / computably
equivalent encodings and is the open half of checkpoint §6(a). -/
theorem hfAmbient_range_indep (C C' : FinitaryCoding L) :
    (hfAmbient C).sentenceRange = (hfAmbient C').sentenceRange :=
  (hfAmbient_adequate C).trans (hfAmbient_adequate C').symm

/-! ## The theory layer

Theory codes are the Ackermann codes all of whose members are sentence codes — so, exactly the
finite sets of sentence codes.  `Nat.finite_ackMem` gives one direction, `Nat.exists_ack_of_finite`
the other. -/

/-- The members of a theory code form a finite set of sentence codes. -/
theorem hfAmbient_members_finite (C : FinitaryCoding L) (a : (hfAmbient C).TheoryCode) :
    ((hfAmbient C).members a).Finite :=
  (Nat.finite_ackMem a.1).preimage Subtype.val_injective.injOn

/-- **The corrected `A`-finiteness characterization.**

Both conjuncts are necessary.  Finiteness comes from `Nat.finite_ackMem`: an Ackermann code has
finitely many bits set.  Containment comes from adequacy: the members are *sentence* codes, and
those decode into the finitary fragment and nowhere else.

The global form `AFinite T ↔ T.Finite` is FALSE here; `not_hfAmbient_aFinite_iff_finite` exhibits
a counterexample. -/
theorem hfAmbient_aFinite_iff (C : FinitaryCoding L) {T : L.Theoryω} :
    (hfAmbient C).AFinite T ↔ T.Finite ∧ T ⊆ finitaryFragment L := by
  classical
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(hfAmbient_members_finite C a).image _,
      TheoryPresentation.AFinite.subset_of_adequate (hfAmbient_adequate C) ⟨a, rfl⟩⟩
  · rintro ⟨hfin, hsub⟩
    have hrange : T ⊆ (hfAmbient C).sentenceRange := by
      rw [hfAmbient_adequate C]; exact hsub
    -- one chosen code per member of `T`
    have hex : ∀ φ : L.Sentenceω, ∃ n : ℕ, φ ∈ T →
        ∃ h : (hfAmbient C).IsSentenceCode n, (hfAmbient C).decodeSentence ⟨n, h⟩ = φ := by
      intro φ
      by_cases hφ : φ ∈ T
      · obtain ⟨s, hs⟩ := hrange hφ
        exact ⟨s.1, fun _ => ⟨s.2, hs⟩⟩
      · exact ⟨0, fun h => absurd h hφ⟩
    choose g hg using hex
    obtain ⟨a, ha⟩ := Nat.exists_ack_of_finite (hfin.image g)
    have hTC : (hfAmbient C).IsTheoryCode a := by
      intro x hx
      obtain ⟨φ, hφT, rfl⟩ := (ha x).mp hx
      exact (hg φ hφT).choose
    refine ⟨⟨a, hTC⟩, ?_⟩
    ext φ
    constructor
    · rintro ⟨s, hsa, rfl⟩
      obtain ⟨ψ, hψT, hgψ⟩ := (ha s.1).mp hsa
      obtain ⟨h, hdec⟩ := hg ψ hψT
      rw [show s = ⟨g ψ, h⟩ from Subtype.ext hgψ.symm, hdec]
      exact hψT
    · intro hφ
      obtain ⟨h, hdec⟩ := hg φ hφ
      exact ⟨⟨g φ, h⟩, (ha _).mpr ⟨φ, hφ, rfl⟩, hdec⟩

/-- **The consumer-friendly form.**  Inside the finitary fragment — which is where every HF
consumer lives — `A`-finiteness *is* ordinary finiteness. -/
theorem hfAmbient_aFinite_iff_of_finitary (C : FinitaryCoding L) {T : L.Theoryω}
    (hT : T ⊆ finitaryFragment L) : (hfAmbient C).AFinite T ↔ T.Finite :=
  (hfAmbient_aFinite_iff C).trans ⟨And.left, fun h => ⟨h, hT⟩⟩

/-- **The distinction is real, not cosmetic.**  A singleton `iInf` theory is finite yet not
`A`-finite, so `AFinite T ↔ T.Finite` genuinely fails.

Exhibiting the counterexample is the point: it is what stops that equation from being adopted
"for convenience". -/
theorem not_hfAmbient_aFinite_iff_finite (C : FinitaryCoding L) (φs : ℕ → L.Sentenceω) :
    ¬((hfAmbient C).AFinite {BoundedFormulaω.iInf φs} ↔
      ({BoundedFormulaω.iInf φs} : L.Theoryω).Finite) := by
  intro h
  obtain ⟨φ₀, hφ₀⟩ :=
    TheoryPresentation.AFinite.subset_of_adequate (hfAmbient_adequate C)
      (h.mpr (Set.finite_singleton _)) rfl
  exact BoundedFormulaω.not_isFirstOrder_iInf φs ⟨φ₀, hφ₀⟩

/-! ## KP closure, discharged

`Nat.mem_ackPair` and `Nat.mem_ackUnion` are exactly the specification laws `WithKP` demands, so
the HF instance is a structure literal.  That it *is* nearly definitional is the signal that
membership was the missing ingredient — the earlier totality-only fields were satisfiable by
`fun _ _ _ => True` and proved nothing. -/

/-- **HF with pairing and union.** -/
noncomputable def hfAmbientKP (C : FinitaryCoding L) : AmbientPresentation.WithKP.{u, v, 0, 0} L where
  toAmbientPresentation := hfAmbient C
  pair := Nat.ackPair
  mem_pair _ _ _ := Nat.mem_ackPair
  union := Nat.ackUnion
  mem_union _ _ := Nat.mem_ackUnion

/-- The KP layer adds laws, not a different presentation. -/
theorem hfAmbientKP_toAmbientPresentation (C : FinitaryCoding L) :
    (hfAmbientKP C).toAmbientPresentation = hfAmbient C := rfl

/-! ## The assembled regression

The public form takes the presentation's **own** `Sigma1`; there is no free `Sig` parameter and no
caller-supplied containment. -/

/-- **Containment for HF, derived from adequacy — no manual hypothesis.**

Universe-general: only the compactness *theorem* below is pinned to `Language.{0, 0}`, and that
restriction belongs to Mathlib's first-order compactness, not to any coding fact. -/
theorem hfAmbient_subset_finitary (C : FinitaryCoding L) {T : L.Theoryω}
    (hT : (hfAmbient C).Sigma1 T) : T ⊆ finitaryFragment L :=
  AmbientPresentation.subset_of_adequate (hfAmbient_adequate C) hT

section Regression

variable {L : Language.{0, 0}}

/-- **Inside the fragment, the Barwise premise IS ordinary finite satisfiability.**

One direction only, and that is the honest shape: a finite subtheory of a finitary theory is
itself finitary, so `hfAmbient_aFinite_iff`'s containment conjunct comes for free and every
ordinarily finite subtheory is `A`-finite.

Only this direction is needed, and it is all that holds without further hypotheses. -/
theorem hfAmbient_isFinitelySatisfiable (C : FinitaryCoding L) {T : L.Theoryω}
    (hT : T ⊆ finitaryFragment L)
    (hfin : (hfAmbient C).toTheoryPresentation.AFinitelySatisfiable T) :
    T.IsFinitelySatisfiable := fun T₀ hT₀ hfin₀ =>
  hfin T₀ hT₀ ((hfAmbient_aFinite_iff C).mpr ⟨hfin₀, hT₀.trans hT⟩)

/-- **The assembled HF compactness theorem**, on the honest route end to end: both premises come
from `hfAmbient`'s own coding data, and the proof goes straight to `finitaryFragment_compact` —
i.e. to Mathlib's first-order compactness.

Containment is discharged internally by `hfAmbient_subset_finitary`; the caller supplies only
Σ-definability and the Barwise premise. -/
theorem hfAmbient_compact (C : FinitaryCoding L) (T : L.Theoryω)
    (hT : (hfAmbient C).ACEnumerable T)
    (hfin : (hfAmbient C).toTheoryPresentation.AFinitelySatisfiable T) : T.IsSatisfiable :=
  have hsub := hfAmbient_subset_finitary C hT
  finitaryFragment_compact hsub (hfAmbient_isFinitelySatisfiable C hsub hfin)

/-- **HF inhabits the compactness interface.** -/
theorem hfAmbient_compactFor (C : FinitaryCoding L) (T : L.Theoryω) :
    (hfAmbient C).CompactFor (finitaryFragment L) T :=
  fun _ hce hfin => hfAmbient_compact C T hce hfin

/-- **Acceptance: the caller never supplies containment.**  `compactFor_of_adequate` derives
`T ⊆ finitaryFragment L` from adequacy plus Σ-definability, so this consumer mentions neither. -/
example (C : FinitaryCoding L) (T : L.Theoryω) (hce : (hfAmbient C).ACEnumerable T)
    (hfin : (hfAmbient C).toTheoryPresentation.AFinitelySatisfiable T) : T.IsSatisfiable :=
  AmbientPresentation.compactFor_of_adequate (hfAmbient_compactFor C T) (hfAmbient_adequate C)
    hce hfin

end Regression

end FirstOrder.Language
