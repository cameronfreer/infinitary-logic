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
# The honest HF ambient instance (issue #19A, steps 2–3)

`Element := ℕ` under Ackermann membership.  Sentence codes are the `enc`-image of the *finitary*
sentences, theory codes are exactly the finite sets of sentence codes, and pairing and union are
ordinary arithmetic.  The four kinds **overlap**, which is correct: in HF every code is a number.

## The `A`-finiteness correction

`hf_aFinite_iff` (on the legacy `hfPresentation`) says `AFinite T ↔ T.Finite` *globally*.  The
honest instance cannot preserve that, and should not:

> theory codes are built from finitary sentence codes, so a finite theory containing an infinitary
> sentence is not an element of HF.

The correct endpoint is `hfAmbient_aFinite_iff`:

```
AFinite T ↔ T.Finite ∧ T ⊆ finitaryFragment L
```

with `hfAmbient_aFinite_iff_of_finitary` as the consumer-friendly form.  This is a **deliberate
#19A API correction**, not an oversight: the old global theorem is a harmless enlargement on
`hfPresentation`'s current compactness domain, but preserving it here would mean encoding
infinitary sentences into HF, which `docs/admissible-19a-checkpoint.md` §1 rules out.
`not_hfAmbient_aFinite_iff_finite` exhibits the failure rather than merely asserting it.

## What remains a placeholder

`FinitaryCoding` stores an injective numbering.  Injectivity gives numbering-independence of the
decoded *range* — hence of adequacy and containment, which is `hfAmbient_range_indep` — but **not**
of `Sigma1`: two injective numberings can disagree about which theories are c.e.  Closing that is
checkpoint §6(a), and it is the next step, not this one.

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
noncomputable def hfAmbient (C : FinitaryCoding L) : AmbientPresentation.{u, v, 0} L where
  Element := ℕ
  -- Ackermann membership: `x ∈ₐ e` iff bit `x` of `e` is set
  Mem := Nat.AckMem
  -- no code names an infinitary family
  IsFamilyCode _ := False
  IsSentenceCode n := ∃ φ₀ : L.Sentence, C.enc φ₀ = n
  -- every natural reads as a partial-recursive code
  IsDefinitionCode _ := True
  decodeSentence e := e.2.choose.toLω
  enumerates d := {s | (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code d.1) s.1).Dom}

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

Compare `hf_aFinite_iff`, whose global `↔ T.Finite` this deliberately replaces; see the module
docstring and `not_hfAmbient_aFinite_iff_finite`. -/
theorem hfAmbient_aFinite_iff (C : FinitaryCoding L) {T : L.Theoryω} :
    (hfAmbient C).AFinite T ↔ T.Finite ∧ T ⊆ finitaryFragment L := by
  classical
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(hfAmbient_members_finite C a).image _,
      AmbientPresentation.AFinite.subset_of_adequate (hfAmbient_adequate C) ⟨a, rfl⟩⟩
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
consumer already lives, by `hf_compact_of_aFinite`'s hypothesis — `A`-finiteness *is* ordinary
finiteness. -/
theorem hfAmbient_aFinite_iff_of_finitary (C : FinitaryCoding L) {T : L.Theoryω}
    (hT : T ⊆ finitaryFragment L) : (hfAmbient C).AFinite T ↔ T.Finite :=
  (hfAmbient_aFinite_iff C).trans ⟨And.left, fun h => ⟨h, hT⟩⟩

/-- **The correction is real, not cosmetic.**  A singleton `iInf` theory is finite yet not
`A`-finite, so the global `hf_aFinite_iff` form genuinely fails for the honest instance.

Exhibiting the counterexample is the point: it is what stops the old equation from being restored
"for compatibility" during the production migration. -/
theorem not_hfAmbient_aFinite_iff_finite (C : FinitaryCoding L) (φs : ℕ → L.Sentenceω) :
    ¬((hfAmbient C).AFinite {BoundedFormulaω.iInf φs} ↔
      ({BoundedFormulaω.iInf φs} : L.Theoryω).Finite) := by
  intro h
  obtain ⟨φ₀, hφ₀⟩ :=
    AmbientPresentation.AFinite.subset_of_adequate (hfAmbient_adequate C)
      (h.mpr (Set.finite_singleton _)) rfl
  exact BoundedFormulaω.not_isFirstOrder_iInf φs ⟨φ₀, hφ₀⟩

/-! ## KP closure, discharged

`Nat.mem_ackPair` and `Nat.mem_ackUnion` are exactly the specification laws `WithKP` demands, so
the HF instance is a structure literal.  That it *is* nearly definitional is the signal that
membership was the missing ingredient — the earlier totality-only fields were satisfiable by
`fun _ _ _ => True` and proved nothing. -/

/-- **HF with pairing and union.** -/
noncomputable def hfAmbientKP (C : FinitaryCoding L) : AmbientPresentation.WithKP.{u, v, 0} L where
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

/-- **The assembled HF compactness regression.**  Containment is discharged internally by
`hfAmbient_subset_finitary`; the caller supplies only the Barwise premise. -/
theorem hfAmbient_compact (C : FinitaryCoding L) (T : L.Theoryω)
    (hT : (hfAmbient C).Sigma1 T)
    (hfin : AFinitelySatisfiable (hfPresentation L) T) : T.IsSatisfiable :=
  hf_compact_of_aFinite (hfAmbient_subset_finitary C hT) hfin

end Regression

end FirstOrder.Language
